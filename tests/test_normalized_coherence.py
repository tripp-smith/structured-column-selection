"""Normalized coherence of a repeated column is 1.

Two copies of a nonzero rational column have inner product equal to the
squared length, so the ratio is `1`. For `m = 2` the triangular block has
Frobenius energy at most `1/4`, while there are `4` rows, and each
completion column is repeated `32 k³` times. This check does not call the
repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F


def test_repeated_column_has_coherence_one():
    column = (F(3, 5), F(-4, 5), F(0, 1))
    energy = sum(x * x for x in column)
    assert energy > 0
    inner = sum(x * x for x in column)
    ratio = abs(inner) / energy
    assert ratio == 1


def test_m2_completion_must_repeat_positive_energy():
    m = 2
    k = m * m
    eps = F(4 * m * m - 1, 4 * m * m + 1)
    coupling = F(2 * m, 4 * m * m + 1)
    alpha = F(1, 2 * k)

    def diag(i):
        return alpha * eps**i

    def entry(i, j):
        if i == j:
            return diag(i)
        if i < j:
            return -coupling * diag(i)
        return F(0)

    frob = sum(entry(i, j) ** 2 for i in range(k) for j in range(k))
    assert frob <= F(1, 4)
    assert k - frob > 0
    repeats = 32 * k**3
    assert repeats >= 2
