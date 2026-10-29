"""Second-pivot split at leverage ratio 32/13.

The columns are the integer pairs `(-4,-4)`, `(0,-5)`, `(3,-2)`,
`(-4,1)`, and `(-3,2)`, divided by `sqrt(50)`. Every column energy lies
in `[13/50, 16/25]`, both rules take column 0 first, every later
residual equals `1/4`, and the increment ratios select column 2 while
max-residual CPQR selects column 1. This recomputes those scores from
the entries. It does not call the repository CPQR code, and it is not
the theorem.
"""

from fractions import Fraction as F


def test_leverage_ratio_32_over_13_splits_the_second_pivot():
    raw = [
        (F(-4), F(-4)),
        (F(0), F(-5)),
        (F(3), F(-2)),
        (F(-4), F(1)),
        (F(-3), F(2)),
    ]
    scale = F(50)

    def energy(column):
        return (column[0] ** 2 + column[1] ** 2) / scale

    def dot(left, right):
        return (left[0] * right[0] + left[1] * right[1]) / scale

    energies = [energy(column) for column in raw]
    assert energies == [F(16, 25), F(1, 2), F(13, 50), F(17, 50), F(13, 50)]
    assert max(energies) / min(energies) == F(32, 13)
    assert min(range(5), key=lambda j: (1 / energies[j], j)) == 0

    pivot = raw[0]
    gram = energy(pivot)

    def residual(column):
        raw_dot = dot(pivot, column)
        return energy(column) - raw_dot * raw_dot / gram

    def ratio(column):
        raw_dot = dot(pivot, column)
        return (1 + (raw_dot / gram) ** 2) / residual(column)

    residuals = [residual(raw[j]) for j in range(1, 5)]
    assert residuals == [F(1, 4), F(1, 4), F(1, 4), F(1, 4)]
    assert min(range(1, 5), key=lambda j: (-residual(raw[j]), j)) == 1

    ratios = [ratio(raw[j]) for j in range(1, 5)]
    assert ratios == [F(89, 16), F(65, 16), F(73, 16), F(65, 16)]
    assert min(range(1, 5), key=lambda j: (ratio(raw[j]), j)) == 2

    row0 = [column[0] for column in raw]
    row1 = [column[1] for column in raw]
    assert sum(x * x for x in row0) == scale
    assert sum(x * x for x in row1) == scale
    assert sum(x * y for x, y in zip(row0, row1)) == 0
