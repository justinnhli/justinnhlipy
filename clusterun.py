#!/usr/bin/env python3

import re
import sys
import subprocess
from ast import literal_eval
from datetime import datetime
from inspect import signature
from itertools import product
from textwrap import dedent

NUM_CORES = 1

class Namespace:

    def __init__(self, **kwargs):
        self._internal_ = {}
        self.update(**kwargs)

    def __eq__(self, other):
        return isinstance(other, Namespace) and self._internal_ == other._internal_

    def __len__(self):
        return len(self._internal_)

    def __add__(self, other):
        updated = self._internal_
        updated.update(other._internal_)
        return Namespace(**updated)

    def __contains__(self, key):
        return key in self._internal_

    def __getitem__(self, key):
        try:
            return getattr(self, key)
        except AttributeError as e:
            raise KeyError(str(e))

    def __setitem__(self, key, value):
        setattr(self, key, value)

    def __delitem__(self, key):
        if key in self._internal_:
            delattr(self, key)
        else:
            raise KeyError(key)

    def __getattr__(self, key):
        if key in self.__dict__:
            return self.__dict__[key]
        if key in self._internal_:
            return self._internal_[key]
        raise AttributeError('{} object has no attribute {}'.format(repr(self.__class__.__name__), repr(key)))

    def __setattr__(self, key, value):
        self.__dict__[key] = value
        if not (key.startswith('_') and key.endswith('_')):
            self._internal_[key] = value

    def __delattr__(self, key):
        if key in self._internal_:
            del self._internal_[key]
            del self.__dict__[key]

    def __repr__(self):
        return 'Namespace(' + ', '.join('{}={}'.format(k, repr(v)) for k, v in sorted(self._internal_.items())) + ')'

    def __str__(self):
        return repr(self)

    def update(self, **kwargs):
        for key, value in kwargs.items():
            # FIXME HACK
            reserved = ['keys', 'values', 'items', 'to_tuple', 'to_csv_row']
            if key in reserved:
                raise KeyError('{} is reserved and is not allowed as a key'.format(repr(key)))
            self._internal_[key] = value
            self.__dict__[key] = value

    def keys(self):
        return self._internal_.keys()

    def values(self):
        return self._internal_.values()

    def items(self):
        return self._internal_.items()

    def _expand_order_(self, order):
        order = list(order)
        return order + sorted(set(self.keys()) - set(order))

    def to_tuple(self, order):
        order = self._expand_order_(order)
        return tuple(self[k] for k in order)

    def to_csv_row(self, order):
        order = self._expand_order_(order)
        return '\t'.join(str(self[k]) for k in order)


class MixedRadix:

    def __init__(self, radixes, init_values=None):
        self.radixes = radixes
        if init_values is None:
            self._state_ = len(radixes) * [0]
        else:
            assert len(radixes) == len(init_values)
            assert all(place < cap for place, cap in zip(init_values, radixes))
            self._state_ = list(init_values)
        self._state_[-1] -= 1

    def __iter__(self):
        return self

    def __next__(self):
        return self.next()

    def next(self, min_place=None):
        if min_place is None:
            min_place = len(self._state_) - 1
        for index in range(min_place + 1, len(self._state_)):
            self._state_[index] = 0
        for index in reversed(range(min_place + 1)):
            if self._state_[index] < self.radixes[index] - 1:
                self._state_[index] += 1
                break
            elif index == 0:
                raise StopIteration
            else:
                self._state_[index] = 0
        return self._state_


class ParameterSpaceIterator:

    def __init__(self, pspace, start=None, end=None):
        if start is None:
            start = {}
        if end is None:
            end = {}
        self.pspace = pspace
        start_indices = len(self.pspace.order) * [0]
        for key, value in start.items():
            assert key in self.pspace.independents, 'unknown start parameter: {}'.format(key)
            assert value in self.pspace.independents[key], \
                'unknown value for start parameter {}: {}'.format(key, repr(value))
            index = self.pspace.order.index(key)
            start_indices[index] = self.pspace.independents[key].index(value)
        self._state_ = MixedRadix(self.pspace.ordered_sizes, start_indices)
        self._end_indices_ = None
        if end:
            self._end_indices_ = len(self.pspace.order) * [0]
            for key, value in end.items():
                assert key in self.pspace.independents, 'unknown end parameter: {}'.format(key)
                assert value in self.pspace.independents[key], \
                    'unknown value for end parameter {}: {}'.format(key, repr(value))
                index = self.pspace.order.index(key)
                self._end_indices_[index] = self.pspace.independents[key].index(value)

    def __iter__(self):
        return self

    def __next__(self):
        conflicts = True
        min_place = len(self.pspace.order) - 1
        while conflicts:
            next_index = self._state_.next(min_place)
            if self._end_indices_ and next_index >= self._end_indices_:
                raise StopIteration
            next_state = self.pspace._get_namespace_from_indices_(next_index)
            conflicts = self._check_filters_(next_state)
            if conflicts:
                min_place = min(
                    max(self.pspace.order.index(parameter) for parameter in parameters) for parameters in conflicts
                )
        return next_state

    def _check_filters_(self, result):
        conflicts = []
        for fn in self.pspace.filters:
            if not fn(**result):
                conflicts.append(set.union(*(self.pspace.dependency_closure[argument] for argument in fn.arguments)))
        return conflicts


class FunctionWrapper:

    def __init__(self, fn):
        self.fn = fn
        self.arguments = tuple(signature(self.fn).parameters.keys())

    def __call__(self, **kwargs):
        return self.fn(**dict((k, v) for k, v in kwargs.items() if k in self.arguments))


class PermutationSpace:

    def __init__(self, order, **kwargs):
        self.independents = {}
        self.dependents = {}
        self.dependents_topo = []
        self.dependency_closure = {}
        self.constants = {}
        self.filters = []
        self.order = list(order)
        for key, value in kwargs.items():
            if hasattr(value, '__iter__') and not isinstance(value, str):
                self.independents[key] = list(value)
            elif hasattr(value, '__call__'):
                self.dependents[key] = FunctionWrapper(value)
            else:
                self.constants[key] = value
        self._check_order_()
        self._calculate_dependents_topo_()
        self._calculate_dependency_closure_()
        self._simplify_order_()

    def __getitem__(self, key):
        if key in self.independents:
            return self.independents[key]
        if key in self.dependents:
            return self.dependents[key]
        if key in self.constants:
            return self.constants[key]
        raise KeyError(f'no parameter {key}; possible choices are {", ".join(self.parameters)}')

    def _calculate_dependents_topo_(self):
        prev_count = 0
        while len(self.dependents_topo) < len(self.dependents):
            for key, fn in self.dependents.items():
                if key in self.dependents_topo:
                    continue
                reachables = self.parameters
                if set(fn.arguments) <= reachables:
                    self.dependents_topo.append(key)
            if len(self.dependents_topo) == prev_count:
                unreachables = set(self.dependents.keys()) - set(self.dependents_topo)
                raise ValueError('undefined arguments in parameter: ' + ', '.join(sorted(unreachables)))
            prev_count = len(self.dependents_topo)

    def _calculate_dependency_closure_(self):
        for key in self.independents:
            self.dependency_closure[key] = set([key])
        for key in self.constants:
            self.dependency_closure[key] = set([key])
        for key in self.dependents_topo:
            self.dependency_closure[key] = set.union(
                set(), *(self.dependency_closure[argument] for argument in self.dependents[key].arguments)
            )

    def _check_order_(self):
        order_set = set(self.order)
        if len(self.order) != len(order_set):
            uniques = set()
            duplicates = set()
            for key in self.independents:
                if key in uniques:
                    duplicates.add(key)
                uniques.add(key)
            raise ValueError('parameter ordering contains duplicates: ' + ', '.join(sorted(duplicates)))
        if order_set != set(self.independents.keys()):
            if not order_set <= self.parameters:
                unreachables = order_set - self.parameters
                raise ValueError('parameter ordering contains undefined parameters: ' + ', '.join(sorted(unreachables)))
            if not set(self.independents.keys()) <= order_set:
                unreachables = set(self.independents.keys()) - order_set
                raise ValueError(
                    'parameter ordering is missing independent parameters: ' + ', '.join(sorted(unreachables))
                )
            if not order_set <= set(self.independents.keys()):
                unreachables = order_set - set(self.independents.keys())
                raise ValueError(
                    'parameter ordering contains non-independent parameters: ' + ', '.join(sorted(unreachables))
                )

    def _simplify_order_(self):
        self.order = [parameter for parameter in self.order if parameter in self.independents]

    @property
    def parameters(self):
        return set.union(
            set(self.independents.keys()),
            set(self.dependents_topo),
            set(self.constants.keys()),
        )

    @property
    def approximate_size(self):
        product = 1
        for values in self.independents.values():
            product *= len(values)
        return product

    @property
    def ordered_sizes(self):
        return [len(self.independents[parameter]) for parameter in self.order]

    def __len__(self):
        return len(list(self.__iter__()))

    def __iter__(self):
        return ParameterSpaceIterator(self)

    def iter_from(self, start=None):
        return ParameterSpaceIterator(self, start=start)

    def iter_until(self, end=None):
        return ParameterSpaceIterator(self, end=end)

    def iter_between(self, start=None, end=None):
        return ParameterSpaceIterator(self, start=start, end=end)

    def iter_only(self, key, value):
        start_index = len(self.order) * [0]
        key_index = self.order.index(key)
        value_index = self.independents[key].index(value)
        start_index[key_index] = value_index
        end_index = MixedRadix(self.ordered_sizes, start_index).next(key_index)
        start = self._get_independents_from_indices_(start_index)
        end = self._get_independents_from_indices_(end_index)
        return ParameterSpaceIterator(self, start=start, end=end)

    def add_filter(self, filter_fn):
        wrapped_function = FunctionWrapper(filter_fn)
        if not set(wrapped_function.arguments) <= self.parameters:
            raise ValueError('filter contains undefined/unreachable arguments')
        self.filters.append(wrapped_function)

    def _get_independents_from_indices_(self, indices):
        assert len(indices) == len(self.order)
        assert all(index < len(self.independents[key]) for index, key in zip(indices, self.order))
        result = Namespace()
        for parameter, index in zip(self.order, indices):
            result[parameter] = self.independents[parameter][index]
        return result

    def _get_namespace_from_indices_(self, indices):
        result = self._get_independents_from_indices_(indices)
        for parameter, value in self.constants.items():
            result[parameter] = value
        for parameter in self.dependents_topo:
            result[parameter] = self.dependents[parameter](**result)
        return result


class PBSJob:

    # For more details, See the \`qsub\` manpage, or
    # http://docs.adaptivecomputing.com/torque/4-1-3/Content/topics/commands/qsub.htm
    TEMPLATE = dedent('''
        #!/bin/sh

        #PBS -N pbs_{name}
        #PBS -q {queue}
        #PBS -l {resources}
        #PBS -v {variables}
        #PBS -r n

        {commands}
    ''').strip()

    def __init__(self, name, commands, queue=None, venv=None):
        self.name = name
        self.commands = commands
        if queue is None:
            self.queue = 'justinli'
        else:
            self.queue = queue
        self.venv = venv
        # these are default for now; future changes may allow on-the-fly allocation
        self.resources = 'nodes=n006.cluster.com:ppn=1,mem=1000mb,file=4gb'

    def _generate_commands(self):
        commands = self.commands
        if self.venv is not None:
            prefixes = [
                'source "/home/justinnhli/.venv/{}/bin/activate"'.format(self.venv),
            ]
            suffixes = [
                'deactivate',
            ]
            commands = prefixes + commands + suffixes
        return '\n'.join(commands)

    def generate_script(self, variables=None):
        """Create a PBS job script.

        Arguments:
            variables (List[Tuple[str, obj]]): List of (key, value).

        Returns:
            str: The PBS job script.
        """
        if variables is None:
            variables = []
        return PBSJob.TEMPLATE.format(
            name=self.name,
            queue=self.queue,
            resources=self.resources,
            variables=','.join(f'{key}={value}' for key, value in variables),
            commands=self._generate_commands(),
        )

    def run(self, variables):
        """Create a single job.

        Arguments:
            variables (List[Tuple[str, obj]]): List of (key, value).
        """
        qsub_command = ['qsub', '-']
        subprocess.run(
            qsub_command,
            input=self.generate_script(variables).encode('utf-8'),
            shell=True,
        )

    def run_all(self, variable_space=None):
        """Create jobs for all variables.

        Arguments:
            variable_space (List[Tuple[str, List[obj]]]): List of (key, values).
        """
        if variable_space is None:
            variable_space = []
        keys = [key for key, values in variable_space]
        space = [values for key, values in variable_space]
        for values in product(*space):
            self.run(list(zip(keys, values)))


def get_parameters(experiment, index=None):
    parameters = list(get_parameter_space(experiment))
    if index is None:
        return parameters
    chunk_size = len(parameters) // NUM_CORES
    remainders = len(parameters) % NUM_CORES
    start = chunk_size * index + min(index, remainders)
    end = chunk_size * (index + 1) + min(index + 1, remainders)
    return parameters[start:end]


def create_jobs_from_parameters(parameter_space, job_name, commands):
    print(40 * '-')
    print('PARAMETERS')
    print()
    for parameter in parameter_space.order:
        values = parameter_space[parameter]
        print(f'{parameter} ({len(values)}):')
        print(f'    {", ".join(repr(param) for param in values)}')
    print()
    print(f'{len(parameter_space.filters)} filters; total size: {len(parameter_space)}')
    print()
    print(40 * '-')
    variables = [
        ('index', list(range(min(len(parameter_space), NUM_CORES)))),
    ]
    run_cli(job_name, variables, commands, verbose=False)


def run_cli(job_name, variables, commands, queue=None, venv=None, verbose=True):
    """Preview the job script and prompt for job start.

    Arguments:
        job_name (str): The name of the job.
        variables (List[Tuple[str, List[obj]]]): List of (key, values).
        commands (List[str]): Commands to run.
        queue (str): The queue to submit the jobs to.
        venv (str): The virtual environment to use.
    """
    pbs_job = PBSJob(job_name, commands, queue=queue, venv=venv)
    if verbose:
        print(pbs_job.generate_script())
        print()
        print(40 * '-')
        print()
        # print variables
        space_size = 1
        warnings = []
        if variables:
            print('variables:')
            for var, vals in variables:
                print('    {}={}'.format(var, repr(vals)))
                for val in vals:
                    if isinstance(val, str) and ',' in val:
                        warnings.append('variable "{}" has string value {} with a comma'.format(var, repr(val)))
                space_size *= len(vals)
        print('total invocations: {}'.format(space_size))
        if warnings:
            print()
            for warning in warnings:
                print('WARNING: ' + warning)
        print()
        print(40 * '-')
        print()
    # prompt confirmation
    try:
        response = input('Run jobs? (y/N) ')
    except KeyboardInterrupt:
        print()
        exit()
    if response.lower().startswith('y'):
        pbs_job.run_all(variables)


def print_help():
    message = 'usage: {} [--<var>=<vals> ...] cmd [arg ...]'.format(
        sys.argv[0]
    )
    print(message)
    exit()


def parse_var(arg, force_list=True):
    var, vals = arg.split('=', maxsplit=1)
    var = var[2:].replace('-', '_')
    if not re.match('^[a-z]([_a-z0-9-]*?[a-z0-9])?$', var):
        raise ValueError('Invalid variable name: "{}"'.format(var))
    try:
        vals = literal_eval(vals)
    except ValueError:
        vals = vals
    if force_list and isinstance(vals, tuple([int, float, str])):
        vals = [vals]
    return var, vals


def parse_args():
    variables = []
    command = None
    kwargs = {}
    last_arg_index = 0
    for i, arg in enumerate(sys.argv[1:], start=1):
        if arg in ('-h', '--help'):
            print_help()
        elif arg.startswith('--'):
            if arg == '--':
                last_arg_index = i
                break
            var, vals = parse_var(arg)
            variables.append([var, vals])
        elif arg.startswith('-'):
            key, val = parse_var(arg, force_list=False)
            kwargs[key] = val
        else:
            break
        last_arg_index = i
    command = ' '.join(sys.argv[last_arg_index + 1:])
    return variables, command, kwargs


def main():
    variables, command, kwargs = parse_args()
    # print script
    job_name = 'from_cmd_' + datetime.now().strftime('%Y%m%d%H%M%S')
    commands = ['cd "$PBS_O_WORKDIR"', command]
    run_cli(job_name, variables, commands, **kwargs)


if __name__ == '__main__':
    main()
