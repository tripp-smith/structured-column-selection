"""Equal column energy, three-column inverse trace, on the 3×3 identity.

Rows are orthonormal and every column energy is 1. The only full Gram is
the identity, whose inverse trace is 3. The three-column bound is 5.
This arithmetic does not call repository CPQR. It is not the theorem.
"""

from fractions import Fraction as F


def three_trace_bound(k, n):
    k = F(k)
    n = F(n)
    two = 2 * (n - 1) / (k - 1)
    step = (1 + (2 * k * (n - 1)) / (n * (k - 1))) * ((n - 2) / (k - 2))
    return two + step


def test_identity_three_trace():
    cols = [(F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1))]
    assert all(sum(c[i] * c[i] for c in cols) == 1 for i in range(3))
    assert all(sum(c[i] * c[j] for c in cols) == 0 for i in range(3) for j in range(3) if i != j)
    assert all(sum(x * x for x in col) == 1 for col in cols)
    assert three_trace_bound(3, 3) == 5
    assert 3 <= three_trace_bound(3, 3)
