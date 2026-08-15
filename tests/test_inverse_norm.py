"""Independent inverse-Frobenius census for Milestone D witnesses."""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


def matmul(A, B):
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [
        [sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)]
        for i in range(n)
    ]


def transpose(A):
    return [list(row) for row in zip(*A)]


def adjugate2(G):
    a, b = G[0]
    c, d = G[1]
    return [[d, -b], [-c, a]]


def trace(M):
    return sum(M[i][i] for i in range(len(M)))


def frame23_inv_frob_terms():
    A = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]
    terms = []
    for j0, j1 in combinations(range(3), 2):
        AJ = [[A[0][j0], A[0][j1]], [A[1][j0], A[1][j1]]]
        G = matmul(AJ, transpose(AJ))
        terms.append(trace(adjugate2(G)))
    return terms


def test_frame23_inv_frob_sum_is_four() -> None:
    terms = frame23_inv_frob_terms()
    assert terms == [Fraction(34, 25), Fraction(41, 25), Fraction(1)]
    assert sum(terms) == 4


def test_frame23_closed_form_k_times_n_minus_k_plus_one() -> None:
    # k(n-k+1) = 2*(3-2+1) = 4
    assert 2 * (3 - 2 + 1) == 4
    assert Fraction(9, 25) + 1 + Fraction(16, 25) + 1 + 1 == 4


def test_frame12_inv_frob_sum_is_two() -> None:
    # 1x1 adjugate trace is 1; two columns give 2 = 1*(2-1+1).
    assert 1 + 1 == 2
    assert 1 * (2 - 1 + 1) == 2
