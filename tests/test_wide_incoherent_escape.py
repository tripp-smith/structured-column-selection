"""Absolute column energies of the outcome-2 triangular block.

For `m = 2` the block is `4×4`. Every entry is the closed form
`wideAlpha`, `wideEps`, and `wideC`, and every column energy is at most
`1 / (2k)`. Off-diagonal inner products obey the same bound by the
squares already computed. The filler cap `k / (32 k³)` is smaller.
This check does not call the repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F


def test_m2_triangular_entries_fit_the_absolute_bound():
    m = 2
    k = m * m
    eps = F(4 * m * m - 1, 4 * m * m + 1)
    coupling = F(2 * m, 4 * m * m + 1)
    alpha = F(1, 2 * k)
    bound = F(1, 2 * k)

    def diag(i):
        return alpha * eps**i

    def entry(i, j):
        if i == j:
            return diag(i)
        if i < j:
            return -coupling * diag(i)
        return F(0)

    for j in range(k):
        energy = sum(entry(i, j) ** 2 for i in range(k))
        assert energy <= bound
    for a in range(k):
        for b in range(a + 1, k):
            inner = sum(entry(i, a) * entry(i, b) for i in range(k))
            assert abs(inner) <= bound
    filler_cap = F(k, 32 * k**3)
    assert filler_cap <= bound
