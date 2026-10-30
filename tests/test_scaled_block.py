"""Scaled leading block: sharp Frobenius bound and the triple-design frame.

`R₀ = wideTriangular m` has diagonal `α ε^i` and strict upper entries
`-c α ε^i` with `k = m²`, `α = 1/(2k)`, `ε = (4m²-1)/(4m²+1)`,
`c = 2m/(4m²+1)`. The checks are the row-structure bound
`‖R₀‖_F² ≤ 5 / (16 k)` in exact rationals for `m = 2, 3, 4`, the threshold
inequality `1 / (4 (k-1)(k-2)) ≤ 9 / (16 k²)` for `5 ≤ k ≤ 200`, and, on
the `m = 3` instance with a floating symmetric completion
`C = (I - R Rᵀ)^{1/2}` of `R = 3 R₀` and the triple design `W`, that every
filler column `C w` has energy below every scaled leading residual and
that the greedy residual pivots are the leading prefix `0, …, k-1`. This
check does not call the repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F

import numpy as np


def succ_above(p, j):
    return j if j < p else j + 1


def triple_columns(n):
    """Integer columns of the weighted signed triple design in `Fin (n+3)`."""
    k = n + 3
    cols = []
    for p in range(k):
        for q in range(k - 1):
            qq = succ_above(p, q)
            for r in range(k - 2):
                rr = succ_above(p, succ_above(q, r))
                for s in (1, -1):
                    for t in (1, -1):
                        v = [0] * k
                        v[p] += 1
                        v[qq] += 2 * s
                        v[rr] += 3 * t
                        cols.append(tuple(v))
    return cols


def wide_triangular(m):
    k = m * m
    eps = F(4 * m * m - 1, 4 * m * m + 1)
    c = F(2 * m, 4 * m * m + 1)
    alpha = F(1, 2 * k)
    diag = [alpha * eps**i for i in range(k)]
    R = [[F(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i == j:
                R[i][j] = diag[i]
            elif i < j:
                R[i][j] = -c * diag[i]
    return R


def frob(R):
    return sum(x * x for row in R for x in row)


def test_sharp_frobenius_bound():
    for m in (2, 3, 4):
        k = m * m
        R = wide_triangular(m)
        assert frob(R) <= F(5, 16 * k)
        assert frob(R) > F(1, 16 * k)  # the bound is within a small constant


def test_threshold_inequality():
    for k in range(5, 201):
        assert F(1, 4 * (k - 1) * (k - 2)) <= F(9, 16 * k * k)
    assert F(1, 4 * 3 * 2) > F(9, 16 * 16)  # fails at k = 4, as the contract says


def test_scaled_triple_frame_m3():
    m = 3
    k = m * m
    R = np.array([[float(x) for x in row] for row in wide_triangular(m)]) * 3.0
    assert 9 * float(frob(wide_triangular(m))) <= 45 / (16 * k)
    G = np.eye(k) - R @ R.T
    evals, evecs = np.linalg.eigh(G)
    assert evals.min() > 0.0
    C = evecs @ np.diag(np.sqrt(evals)) @ evecs.T
    assert np.allclose(C, C.T)
    assert np.allclose(R @ R.T + C @ C.T, np.eye(k), atol=1e-12)
    n = k - 3
    cols = triple_columns(n)
    Z = 56 * (n + 2) * (n + 1)
    W = np.array(cols, dtype=float).T / np.sqrt(Z)
    assert W.shape == (k, 4 * k * (k - 1) * (k - 2))
    assert np.allclose(W @ W.T, np.eye(k), atol=1e-12)
    A = np.hstack([R, C @ W])
    assert np.allclose(A @ A.T, np.eye(k), atol=1e-12)
    # Filler energies are below the contraction bound and below the thresholds.
    filler_energy = (C @ W) ** 2
    filler_energy = filler_energy.sum(axis=0)
    design_energy = (W**2).sum(axis=0)
    assert np.all(filler_energy <= design_energy + 1e-12)
    diag = np.diag(R)
    assert np.all(filler_energy < diag.min() ** 2)
    # Greedy residual pivots: repeatedly take the largest residual column.
    Q = np.zeros((k, 0))
    chosen = []
    for _ in range(k):
        resid = A - Q @ (Q.T @ A)
        energies = (resid**2).sum(axis=0)
        j = int(np.argmax(energies))
        chosen.append(j)
        q = resid[:, j] / np.linalg.norm(resid[:, j])
        Q = np.hstack([Q, q[:, None]])
    assert chosen == list(range(k))
