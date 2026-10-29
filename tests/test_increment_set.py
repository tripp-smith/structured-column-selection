"""Least-index increment pivot on the rational 2×3 frame.

Empty-block scores are reciprocal column energies. After column 0, the
Schur scores pick column 2. The selected Gram inverse trace is
1 + 25/16, and k(n - k + 1) = 4. This does not call CPQR and is not
the theorem.
"""

from fractions import Fraction as F


def test_increment_scores_select_columns_0_and_2():
    columns = [
        [F(1), F(0)],
        [F(0), F(3, 5)],
        [F(0), F(4, 5)],
    ]

    def energy(column):
        return column[0] ** 2 + column[1] ** 2

    empty_scores = [1 / energy(column) for column in columns]
    assert empty_scores[0] == 1
    assert empty_scores[1] == F(25, 9)
    assert empty_scores[2] == F(25, 16)
    assert min(range(3), key=lambda j: (empty_scores[j], j)) == 0

    # Column 0 is orthogonal to the other two, so both Schur complements
    # are the raw column energies and both coefficients vanish.
    later_scores = [1 / energy(columns[1]), 1 / energy(columns[2])]
    assert later_scores == [F(25, 9), F(25, 16)]
    assert min((1, 2), key=lambda j: (1 / energy(columns[j]), j)) == 2

    gram = [[F(1), F(0)], [F(0), F(16, 25)]]
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    trace = gram[1][1] / det + gram[0][0] / det
    assert trace == F(1) + F(25, 16)
    assert trace <= F(2) * (F(3) - F(2) + F(1))
