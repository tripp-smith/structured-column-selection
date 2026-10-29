"""Zero coefficient makes the residual and increment scores agree.

On the rational 2×3 frame, column 0 is orthogonal to the other two
columns. After it is selected, both scores are determined by the
residual, and both least-index rules pick column 2. This recomputes
the dots from the entries. It is not the theorem.
"""

from fractions import Fraction as F


def test_zero_coefficient_picks_the_same_column():
    columns = [
        [F(1), F(0)],
        [F(0), F(3, 5)],
        [F(0), F(4, 5)],
    ]

    def dot(left, right):
        return left[0] * right[0] + left[1] * right[1]

    def energy(column):
        return dot(column, column)

    assert dot(columns[0], columns[1]) == 0
    assert dot(columns[0], columns[2]) == 0

    residuals = [energy(columns[1]), energy(columns[2])]
    assert residuals == [F(9, 25), F(16, 25)]
    cpqr = min((1, 2), key=lambda j: (-energy(columns[j]), j))
    increment = min((1, 2), key=lambda j: (1 / energy(columns[j]), j))
    assert cpqr == 2
    assert increment == 2
