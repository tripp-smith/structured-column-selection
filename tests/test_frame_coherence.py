"""Filler-pair coherence of the scaled triple-design frame at m = 3.

The frame is `[3 R₀ | C W]` with `C = (I - 9 R₀ R₀ᵀ)^{1/2}` and `W` the
weighted signed triple design. `ε = 9 ‖R₀‖_F²` is computed in exact
rationals. Every filler–filler normalized ratio is checked against
`(13/14 + ε)/(1 - ε)`, and every leading–filler ratio against
`(3(1 + 1/3)/√14 + ε)/√(1 - ε)`. Those formulas may exceed 1; the ratios
on this instance are also checked to be strictly below 1. This check does
not call the repository CPQR code, and it is not the theorem.
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


def frame_m3():
    m = 3
    k = m * m
    R0 = wide_triangular(m)
    eps = 9 * frob(R0)
    R = np.array([[float(x) for x in row] for row in R0]) * 3.0
    G = np.eye(k) - R @ R.T
    evals, evecs = np.linalg.eigh(G)
    C = evecs @ np.diag(np.sqrt(np.clip(evals, 0.0, None))) @ evecs.T
    n = k - 3
    Z = 56 * (n + 2) * (n + 1)
    W = np.array(triple_columns(n), dtype=float).T / np.sqrt(Z)
    A = np.hstack([R, C @ W])
    return A, k, float(eps)


def _pair_ratios(left, right):
    dots = left.T @ right
    el = (left**2).sum(axis=0)
    er = (right**2).sum(axis=0)
    scale = np.sqrt(el[:, None] * er[None, :])
    return np.abs(dots) / scale, el, er


def test_filler_filler_formula():
    A, k, eps = frame_m3()
    fillers = A[:, k:]
    ratios, energies, _ = _pair_ratios(fillers, fillers)
    np.fill_diagonal(ratios, 0.0)
    assert np.all(energies > 1e-8)
    bound = (13 / 14 + eps) / (1 - eps)
    assert eps < 1
    assert np.all(ratios <= bound + 1e-8)


def test_leading_filler_formula():
    A, k, eps = frame_m3()
    leading = A[:, :k]
    fillers = A[:, k:]
    ratios, el, ef = _pair_ratios(leading, fillers)
    assert np.all(el > 1e-8)
    assert np.all(ef > 1e-8)
    theta = 3 * (1 + 1 / 3) / np.sqrt(14)
    bound = (theta + eps) / np.sqrt(1 - eps)
    assert np.all(ratios <= bound + 1e-8)


def test_ratios_below_one():
    A, k, _eps = frame_m3()
    leading = A[:, :k]
    fillers = A[:, k:]
    filler_ratios, _, _ = _pair_ratios(fillers, fillers)
    np.fill_diagonal(filler_ratios, 0.0)
    leading_ratios, _, _ = _pair_ratios(leading, fillers)
    assert filler_ratios.max() < 1
    assert leading_ratios.max() < 1
