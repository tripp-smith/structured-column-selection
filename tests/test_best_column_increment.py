"""Best unused inverse-trace increment on one rational frame.

After selecting column 0 of the 2×3 frame, column 2 has increment 25/16.
The comparison bound is 2. This does not call CPQR and is not the theorem.
"""

from fractions import Fraction as F


def test_column_two_increment_is_at_most_the_average():
    residual = F(4, 5) ** 2
    score = F(0)
    ratio = (1 + score) / residual
    bound = (F(3 - 1) + (F(1) - F(1))) / F(2 - 1)
    assert ratio == F(25, 16)
    assert bound == 2
    assert ratio <= bound
