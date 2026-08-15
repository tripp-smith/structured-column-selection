"""Column-pivoted QR using the same Gram-determinant residual as Lean."""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence


Matrix = list[list[Fraction]]


def transpose(A: Matrix) -> Matrix:
    return [list(row) for row in zip(*A)]


def matmul(A: Matrix, B: Matrix) -> Matrix:
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [
        [sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)]
        for i in range(n)
    ]


def det(G: Matrix) -> Fraction:
    n = len(G)
    if n == 0:
        return Fraction(1)
    if n == 1:
        return G[0][0]
    if n == 2:
        return G[0][0] * G[1][1] - G[0][1] * G[1][0]
    # Laplace expansion; census instances stay small.
    total = Fraction(0)
    for j in range(n):
        minor = [
            [G[i][c] for c in range(n) if c != j]
            for i in range(1, n)
        ]
        sign = Fraction(1) if j % 2 == 0 else Fraction(-1)
        total += sign * G[0][j] * det(minor)
    return total


def selected_cols(A: Matrix, J: Sequence[int]) -> Matrix:
    cols = sorted(J)
    return [[row[j] for j in cols] for row in A]


def residual_sq(A: Matrix, J: Sequence[int], j: int) -> Fraction:
    B = selected_cols(A, J)
    G = matmul(transpose(B), B)
    gdet = det(G)
    if gdet == 0:
        return Fraction(0)
    B2 = selected_cols(A, list(J) + [j])
    G2 = matmul(transpose(B2), B2)
    return det(G2) / gdet


def cpqr_set(A: Matrix, k: int | None = None) -> list[int]:
    """Greedy CPQR column indices, ties broken by smallest index."""
    rows = len(A)
    cols = len(A[0])
    steps = rows if k is None else k
    chosen: list[int] = []
    unused = set(range(cols))
    for _ in range(steps):
        if not unused:
            break
        scores = {j: residual_sq(A, chosen, j) for j in unused}
        best = max(scores.values())
        if best <= 0:
            break
        j = min(j for j, s in scores.items() if s == best)
        chosen.append(j)
        unused.remove(j)
    return sorted(chosen)


def op_norm_2x2_inverse(AJ: Matrix) -> Fraction:
    """Spectral norm of a 2×2 inverse, for the running rational witness."""
    a, b = AJ[0]
    c, d = AJ[1]
    detAJ = a * d - b * c
    inv = [[d / detAJ, -b / detAJ], [-c / detAJ, a / detAJ]]
    # For a diagonal positive matrix this is the max |diagonal|.
    G = matmul(transpose(inv), inv)
    # eigenvalues of SPD 2×2: closed form
    tr = G[0][0] + G[1][1]
    disc = (G[0][0] - G[1][1]) ** 2 + 4 * G[0][1] * G[1][0]
    # disc is a square for the witness; return sqrt of larger eigenvalue
    # by evaluating the exact diagonal case when off-diagonals vanish.
    if G[0][1] == 0 and G[1][0] == 0:
        return max(G[0][0], G[1][1]) ** Fraction(1, 2) if False else max(
            abs(inv[0][0]), abs(inv[1][1])
        )
    # fallback: larger eigenvalue of G is ‖inv‖₂²
    lam = (tr + _sqrt_fraction(disc)) / 2
    return _sqrt_fraction(lam)


def _sqrt_fraction(x: Fraction) -> Fraction:
    if x < 0:
        raise ValueError(x)
    # exact integer square root of num/den when both are squares
    n = x.numerator
    d = x.denominator

    def isqrt(v: int) -> int:
        r = int(v**0.5)
        while r * r < v:
            r += 1
        while r * r > v:
            r -= 1
        if r * r != v:
            raise ValueError(f"{v} is not a square")
        return r

    return Fraction(isqrt(n), isqrt(d))
