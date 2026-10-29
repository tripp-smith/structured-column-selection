"""The triangular prefix of the adverse family is not column-orthogonal.

For m = 2 the leading columns have inner product
-(4/17) * (1/8)^2. This recomputes that scalar from the closed form.
It is not the theorem.
"""

from fractions import Fraction as F


def prefix_inner(m):
    k = m * m
    c = F(2 * m, 4 * k + 1)
    alpha = F(1, 2 * k)
    return -c * alpha * alpha


def test_wide_prefix_inner_is_nonzero():
    assert prefix_inner(2) == -F(4, 17) * F(1, 8) ** 2
    assert prefix_inner(2) != 0
    assert prefix_inner(3) != 0
