"""Inverse-trace bound for one k-column subset of the rational 2×3 frame.

Columns {0, 2} have Gram inverse trace 1 + 25/16, and k(n - k + 1) = 4.
This does not call CPQR and is not the theorem.
"""

from fractions import Fraction as F


def test_two_columns_meet_the_induction_bound():
    gram = [[F(1), F(0)], [F(0), F(16, 25)]]
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    inverse = [
        [gram[1][1] / det, -gram[0][1] / det],
        [-gram[1][0] / det, gram[0][0] / det],
    ]
    trace = inverse[0][0] + inverse[1][1]
    bound = F(2) * (F(3) - F(2) + F(1))
    assert trace == F(1) + F(25, 16)
    assert bound == 4
    assert trace <= bound
