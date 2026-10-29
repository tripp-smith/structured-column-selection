"""Max-residual CPQR and the increment pivot on a rational 2×5 frame.

Column energies pick index 0 for both rules. After that column, the
largest residual is 2/5 at indices 1 and 2, so the least index is 1.
The increment ratios pick index 2. This recomputes those scores from
the entries. It does not call the repository CPQR code, and it is not
the theorem.
"""

from fractions import Fraction as F


def test_cpqr_and_increment_select_different_columns():
    rows = [
        [F(1), F(-3), F(-2), F(-1), F(-1)],
        [F(-3), F(1), F(-2), F(-1), F(-1)],
    ]
    scale = F(1, 4)
    columns = [[scale * rows[i][j] for i in range(2)] for j in range(5)]

    def dot(left, right):
        return left[0] * right[0] + left[1] * right[1]

    def row_dot(left, right):
        return sum(a * b for a, b in zip(left, right))

    def energy(column):
        return dot(column, column)

    row0 = [columns[j][0] for j in range(5)]
    row1 = [columns[j][1] for j in range(5)]
    assert row_dot(row0, row0) == 1
    assert row_dot(row1, row1) == 1
    assert row_dot(row0, row1) == 0

    energies = [energy(column) for column in columns]
    assert energies == [F(5, 8), F(5, 8), F(1, 2), F(1, 8), F(1, 8)]
    assert min(range(5), key=lambda j: (1 / energies[j], j)) == 0

    pivot = columns[0]
    gram = energy(pivot)

    def residual(column):
        raw = dot(pivot, column)
        return energy(column) - raw * raw / gram

    def ratio(column):
        raw = dot(pivot, column)
        coeff_sq = (raw / gram) ** 2
        return (1 + coeff_sq) / residual(column)

    residuals = [residual(columns[j]) for j in range(1, 5)]
    assert residuals == [F(2, 5), F(2, 5), F(1, 10), F(1, 10)]
    assert min(range(1, 5), key=lambda j: (-residual(columns[j]), j)) == 1

    ratios = [ratio(columns[j]) for j in range(1, 5)]
    assert ratios == [F(17, 5), F(29, 10), F(52, 5), F(52, 5)]
    assert min(range(1, 5), key=lambda j: (ratio(columns[j]), j)) == 2
