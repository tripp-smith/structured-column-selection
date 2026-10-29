"""One inverse-trace growth step on the rational 2×3 frame.

Column 0 has inverse trace 1, at most 3/2. Appending column 2 produces
inverse trace 1 + 25/16, at most 4. This does not call CPQR and is not
the theorem.
"""

from fractions import Fraction as F


def test_appended_inverse_trace_meets_the_next_bound():
    gram = [[F(1), F(0)], [F(0), F(16, 25)]]
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    inverse = [
        [gram[1][1] / det, -gram[0][1] / det],
        [-gram[1][0] / det, gram[0][0] / det],
    ]
    trace = inverse[0][0] + inverse[1][1]
    assert F(1) <= F(3, 2)
    assert trace == F(1) + F(25, 16)
    assert trace <= F(4)
