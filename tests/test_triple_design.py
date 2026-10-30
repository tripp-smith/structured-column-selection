"""Weighted signed triple design in exact rationals.

For `k = n + 3` the columns are indexed by `(p, q, r, s, t)` with
`p in Fin k`, `q in Fin (k-1)`, `r in Fin (k-2)`, signs `s, t in {+1, -1}`.
With `q' = succAbove(p, q)` and `r' = succAbove(p, succAbove(q, r))` the
integer column is `e_p + 2 s e_{q'} + 3 t e_{r'}`. The real design divides
by `sqrt(56 (n+2)(n+1))`; here the normalization is kept as its square
`Z = 56 (n+2)(n+1)` so every check is exact.

Checks: `V Vᵀ = Z I` (so `W Wᵀ = I`), every column has `|v|² = 14` (so
energy `14 / Z = 1 / (4 (n+2)(n+1))`), every pair of distinct columns has
integer inner product of absolute value at most `13` (normalized
coherence at most `13/14`), and the bound `13` is attained. This check
does not call the repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F
from itertools import product


def succ_above(p, j):
    """`Fin.succAbove p j`: the `j`-th element of `Fin (m+1)` skipping `p`."""
    return j if j < p else j + 1


def triple_columns(n):
    k = n + 3
    cols = []
    for p in range(k):
        for q in range(k - 1):
            qq = succ_above(p, q)
            for r in range(k - 2):
                rr = succ_above(p, succ_above(q, r))
                assert len({p, qq, rr}) == 3
                for s in (1, -1):
                    for t in (1, -1):
                        v = [0] * k
                        v[p] += 1
                        v[qq] += 2 * s
                        v[rr] += 3 * t
                        cols.append(tuple(v))
    return cols


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def check_design(n):
    k = n + 3
    cols = triple_columns(n)
    count = 4 * (n + 3) * (n + 2) * (n + 1)
    assert len(cols) == count
    assert len(set(cols)) == count, "columns must be pairwise distinct"
    z = 56 * (n + 2) * (n + 1)
    # Row Gram matrix V Vᵀ = Z I.
    for i in range(k):
        for j in range(k):
            g = sum(v[i] * v[j] for v in cols)
            assert g == (z if i == j else 0), (n, i, j, g)
    # Column energy 14 / Z = 1 / (4 (n+2)(n+1)).
    for v in cols:
        assert dot(v, v) == 14
        assert F(14, z) == F(1, 4 * (n + 2) * (n + 1))
    # Pairwise inner product bound and attainment.
    worst = 0
    for a in range(len(cols)):
        for b in range(a + 1, len(cols)):
            ip = abs(dot(cols[a], cols[b]))
            assert ip <= 13, (n, cols[a], cols[b], ip)
            worst = max(worst, ip)
    return worst


def test_triple_design_small_dimensions():
    for n in range(0, 3):
        worst = check_design(n)
        assert worst == 13, (n, worst)


def test_triple_design_k6_sampled_pairs():
    n = 3
    cols = triple_columns(n)
    k = n + 3
    z = 56 * (n + 2) * (n + 1)
    assert len(cols) == 4 * 6 * 5 * 4
    for i in range(k):
        for j in range(k):
            g = sum(v[i] * v[j] for v in cols)
            assert g == (z if i == j else 0)
    for v in cols:
        assert dot(v, v) == 14
    # Full pairwise check on a deterministic stride of column pairs.
    stride = 7
    for a in range(0, len(cols), stride):
        for b in range(len(cols)):
            if a != b:
                assert abs(dot(cols[a], cols[b])) <= 13


def test_coherence_witness():
    # Swapping the weights 1 and 2 attains 13: (1, 2, 3) against (2, 1, 3).
    u = (1, 2, 3)
    v = (2, 1, 3)
    assert dot(u, v) == 13
    assert dot(u, u) == 14 and dot(v, v) == 14
    assert F(13, 14) == F(dot(u, v), 14)
