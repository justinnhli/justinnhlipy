#!/usr/bin/env python3

from collections import namedtuple
from statistics import mean
from itertools import zip_longest
from fractions import Fraction

Grade = namedtuple('Grade', 'letter, gpa, percent, fraction')
Conversion = namedtuple('Conversion', 'letter, gpa, minimum, representative')


def mixed(whole, numer=0, denom=1, percent=False):
    result = Fraction(whole * denom + numer, denom)
    if percent:
        return result / 100
    else:
        return result


LETTERS = ['F', 'D', 'D+', 'C-', 'C', 'C+', 'B-', 'B', 'B+', 'A-', 'A']
GPAS = [0, *(float(Fraction(numer, 3)) for numer in range(3, 3 * 4 + 1))]
BOUNDS = [
    mixed(00, 0, 1, percent=True),
    mixed(60, 0, 1, percent=True),
    mixed(65, 0, 1, percent=True),
    mixed(70, 0, 3, percent=True),
    mixed(73, 1, 3, percent=True),
    mixed(76, 2, 3, percent=True),
    mixed(80, 0, 3, percent=True),
    mixed(83, 1, 3, percent=True),
    mixed(86, 2, 3, percent=True),
    mixed(90, 0, 1, percent=True),
    mixed(95, 0, 1, percent=True),
]


def create_conversations(bounds=None):
    if bounds is None:
        bounds = BOUNDS
    bounds = tuple(bounds)
    if len(bounds) != 11:
        raise ValueError(f'expected 11 lower bounds, but got {len(bounds)}')
    if bounds[0] != 0:
        raise ValueError(f'lower bound of first grade is not 0: {bounds[0]}')
    if all(0 <= bound <= 1 for bound in bounds):
        scale = Fraction(1)
    else:
        scale = Fraction(1, 100)
    bounds = [
        scale * (bound if isinstance(bound, Fraction) else Fraction(bound))
        for bound in bounds
    ]
    reps = [
        Fraction(0),
        *(
            (lower + upper) / 2 for lower, upper
            in zip(bounds[1:], (*bounds[2:], 1))
        ),
    ]
    return [Conversion(*parts) for parts in zip(LETTERS, GPAS, bounds, reps)]


def from_letter(orig_letters, bounds=None):
    conversion = create_conversations(bounds)
    fractions = []
    for orig_letter in orig_letters.split('/'):
        if orig_letter == '':
            orig_letter = 'F'
        found = False
        for letter, _, _, frac in conversion:
            if orig_letter == letter:
                fractions.append(frac)
                found = True
                break
        if not found:
            raise ValueError(f'invalid letter grade "{orig_letter}"')
    mean_frac = mean(fractions)
    return from_fraction(mean_frac.numerator, mean_frac.denominator)


def from_fraction(numerator, denominator, bounds=None):
    conversion = create_conversations(bounds)
    if numerator < 0 or denominator < 0:
        raise ValueError(' '.join([
            'both numerator and denominator must be positive',
            f'but got {numerator} and {denominator}',
        ]))
    frac = Fraction(numerator, denominator)
    if not 0 <= frac <= 1:
        raise ValueError(f'invalid fraction "{frac}"')
    for letter, gpa, minimum, _ in reversed(conversion):
        if frac >= minimum:
            return Grade(letter, gpa, float(frac), frac)
    letter = conversion[0].letter
    gpa = conversion[0].gpa
    return Grade(letter, gpa, float(frac), frac)


def from_percent(percent, bounds=None):
    conversion = create_conversations(bounds)
    if not 0 <= percent <= 1:
        raise ValueError(f'invalid percentage "{repr(percent)}"')
    for letter, gpa, minimum, _ in reversed(conversion):
        if percent >= minimum:
            return Grade(letter, gpa, percent, Fraction('{:.5f}'.format(percent)))
    letter = conversion[0].letter
    gpa = conversion[0].gpa
    return Grade(letter, gpa, percent, Fraction('{:.5f}'.format(percent)))


def from_gpa(orig_gpa, bounds=None):
    conversion = create_conversations(bounds)
    if not 0 <= orig_gpa <= 4:
        raise ValueError(f'invalid GPA "{orig_gpa}"')
    prev_gpa = conversion[0].gpa
    for letter, gpa, _, frac in conversion:
        if prev_gpa <= orig_gpa < gpa:
            return Grade(letter, orig_gpa, float(frac), frac)
    letter = conversion[-1].letter
    frac = conversion[-1].frac
    return Grade(letter, orig_gpa, float(frac), frac)


assert from_letter('B-/B+').fraction == Fraction(17, 20), from_letter('B-/B+')

class Weights:

    def __init__(self, components, total=Fraction(1)):
        if not isinstance(total, Fraction):
            raise ValueError('Total should be given as a Fraction')
        self.total = total
        self.components = []
        self.weights = {}
        self.subcomponents = {}
        for component, weight in components:
            self.components.append(component)
            if isinstance(weight, Fraction):
                self.weights[component] = weight
                continue
            is_subcomponent = (
                isinstance(weight, (list, tuple)) and
                len(weight) == 2 and
                isinstance(weight[0], Fraction) and
                isinstance(weight[1], Weights)
            )
            if is_subcomponent:
                self.weights[component] = weight[0]
                self.subcomponents[component] = weight[1]
                continue
            raise ValueError(f'weight of "{component}" must be Fraction or [Fraction, Weights]')
        if total and sum(self.weights.values()) != total:
            total = sum(self.weights.values())
            equation = f'{total} = ' + ' + '.join(str(value) for value in self.weights.values())
            raise ValueError(f'weights should sum to {total} but instead sum to {equation}')

    def __getitem__(self, key):
        if isinstance(key, (list, tuple)):
            if len(key) == 1:
                return self.weights[key[0]]
            else:
                return self.weights[key[0]] * self.subcomponents[key[0]][key[1:]]
        else:
            return self.weights[key]

    def __len__(self):
        return sum(1 for _ in self)

    def __iter__(self):
        for component in self.components:
            if component in self.subcomponents:
                for rest in self.subcomponents[component]:
                    if isinstance(rest, (list, tuple)):
                        yield (component, *rest)
                    else:
                        yield (component, rest)
            else:
                yield (component,)

    def __str__(self):
        lines = []
        prev_prefix = ()
        for key in self:
            for depth, (prev, curr) in enumerate(zip_longest(prev_prefix, key[:-1])):
                if prev == curr:
                    continue
                indent = depth * '    '
                curr_key = key[:depth + 1]
                lines.append(' '.join([
                    f'{indent}{curr}',
                    f'({float(self[curr_key]):.2%})',
                ]))
            indent = (len(key) - 1) * '    '
            lines.append(' '.join([
                f'{indent}{key[-1]}',
                f'({float(self.local_weight(key)):.2%})',
            ]))
            prev_prefix = key[:-1]
        return '\n'.join(lines)

    def keys(self):
        yield from self

    def values(self):
        for key in self:
            yield self[key]

    def items(self):
        for key in self:
            yield key, self[key]

    def local_weight(self, key):
        if isinstance(key, (list, tuple)) and len(key) != 1:
            return self.subcomponents[key[0]].local_weight(key[1:])
        else:
            return self.weights[key[0]]

    def apply(self, *grades):
        return WeightedGrade(self, *grades)


class WeightedGrade:

    def __init__(self, weights, *grades):
        if len(grades) != len(weights):
            raise ValueError('expected {len(weights)} grades but got {len(grades)}')
        self.weights = weights
        self.grades = {}
        for key, grade in zip(self.weights, grades):
            if not isinstance(grade, Grade):
                raise ValueError('grades should be given as Grades')
            self.grades[key] = grade

    def __str__(self):
        lines = []
        prev_prefix = ()
        for key in self.weights:
            for depth, (prev, curr) in enumerate(zip_longest(prev_prefix, key[:-1])):
                if curr is None or prev == curr:
                    continue
                indent = depth * '    '
                curr_key = key[:depth + 1]
                lines.append(' '.join([
                    f'{indent}{curr}',
                    f'({float(self.weights[curr_key]):.2%})',
                ]))
            indent = (len(key) - 1) * '    '
            lines.append(' '.join([
                f'{indent}{key[-1]}',
                f'({float(self.weights.local_weight(key)):.2%}):',
                f'{self.grades[key].letter}',
                f'({self.grades[key].percent:.2%})',
            ]))
            prev_prefix = key[:-1]
        return '\n'.join(lines)

    @property
    def current(self):
        if self.weights.total < 1:
            frac = self.minimum.fraction / self.weights.total
        else:
            frac = self.minimum.fraction
        return from_fraction(frac.numerator, frac.denominator)

    @property
    def minimum(self):
        total = 0
        for key, weight in self.weights.items():
            total += weight * self.grades[key].fraction
        return from_fraction(total.numerator, total.denominator)

    @property
    def maximum(self):
        remaining = max(1 - self.weights.total, 0)
        frac = self.minimum.fraction + remaining
        return from_fraction(frac.numerator, frac.denominator)


def test():
    weights = Weights(
        [
            ['Reading', Fraction(15, 100)],
            ['Research Presentation', Fraction(5, 100)],
            ['Design Critique', Fraction(10, 100)],
            ['Mobile Design', [
                Fraction(40, 300),
                Weights([
                    ['Design/Process', Fraction(3, 4)],
                    ['Blog', Fraction(1, 4)],
                ]),
            ]],
            ['Conversational Design', [
                Fraction(40, 300),
                Weights([
                    ['Design/Process', Fraction(3, 4)],
                    ['Blog', Fraction(1, 4)],
                ]),
            ]],
            ['Gestural Design', [
                Fraction(40, 300),
                Weights([
                    ['Design/Process', Fraction(2, 3)],
                    ['Blog', Fraction(1, 3)],
                ]),
            ]],
        ],
        total=Fraction(70, 100),
    )

    grade = weights.apply(
        from_percent(1), # reading
        from_percent(1), # research
        from_letter('A'), # critique
        from_letter('A'), # mobile design
        from_letter('A-'), # mobile blog
        from_letter('B'), # conversation design
        from_letter('A-/B+'), # conversation blog
        from_letter('A-'), # gesture design
        from_letter('A-'), # gesture blog
    )

    print(weights)
    print()
    print(f'Current: {grade.current.letter} ({grade.current.percent:.2%})')
    print(f'Minimum: {grade.minimum.letter} ({grade.minimum.percent:.2%})')
    print(f'Maximum: {grade.maximum.letter} ({grade.maximum.percent:.2%})')
    print()
    print(grade)
