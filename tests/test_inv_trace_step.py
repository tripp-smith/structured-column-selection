"""Exact inverse-trace increment for one appended column.

This recomputes a 2×2 Gram inverse by cofactors. It is not the Lean theorem.
"""

from fractions import Fraction as F


def test_two_by_two_inverse_trace_is_one_plus_twenty_five_ninths():
    gram = [[F(1), F(0)], [F(0), F(9, 25)]]
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    inverse = [
        [gram[1][1] / det, -gram[0][1] / det],
        [-gram[1][0] / det, gram[0][0] / det],
    ]
    trace = inverse[0][0] + inverse[1][1]
    assert trace == F(1) + F(25, 9)
    assert all(isinstance(entry, F) for row in inverse for entry in row)
