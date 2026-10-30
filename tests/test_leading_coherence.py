"""Leading–leading coherence of the triangular block, in exact rationals.

For `m = 2, 3, 4`, every pair `i < j` of columns of `wideTriangular m` is
checked by comparing squares,
`inner^2 * 1 ≤ (1/2 + 1/m)^2 * energy_i * energy_j`, and the same
comparison is checked for `scaledBlock = 3 * wideTriangular m`. This check
does not call the repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F


def wide_triangular(m):
    k = m * m
    eps = F(4 * m * m - 1, 4 * m * m + 1)
    c = F(2 * m, 4 * m * m + 1)
    alpha = F(1, 2 * k)
    diag = [alpha * eps**i for i in range(k)]
    rows = [[F(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i == j:
                rows[i][j] = diag[i]
            elif i < j:
                rows[i][j] = -c * diag[i]
    return rows


def column(rows, j):
    return [row[j] for row in rows]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def energy(v):
    return sum(a * a for a in v)


def check_pairs(rows, m):
    k = len(rows)
    rho = F(1, 2) + F(1, m)
    rho2 = rho * rho
    saw_nonzero = False
    for i in range(k):
        ci = column(rows, i)
        ei = energy(ci)
        assert ei > 0
        for j in range(i + 1, k):
            cj = column(rows, j)
            inner = dot(ci, cj)
            ej = energy(cj)
            assert ej > 0
            assert inner * inner * 1 <= rho2 * ei * ej
            if inner != 0:
                saw_nonzero = True
    assert saw_nonzero


def test_wide_leading_pairs():
    for m in (2, 3, 4):
        check_pairs(wide_triangular(m), m)


def test_scaled_leading_pairs():
    for m in (2, 3, 4):
        rows = wide_triangular(m)
        scaled = [[3 * entry for entry in row] for row in rows]
        check_pairs(scaled, m)
