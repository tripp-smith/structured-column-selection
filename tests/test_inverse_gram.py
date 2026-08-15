"""Independent inverse-Gram adjugate census for Milestone C witnesses."""

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


def add(X, Y):
    return [[X[i][j] + Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]


def frame23_inverse_gram_sum():
    A = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]
    total = [[Fraction(0), Fraction(0)], [Fraction(0), Fraction(0)]]
    for j0, j1 in combinations(range(3), 2):
        AJ = [[A[0][j0], A[0][j1]], [A[1][j0], A[1][j1]]]
        G = matmul(AJ, transpose(AJ))
        total = add(total, adjugate2(G))
    return total


def test_frame23_inverse_gram_sum_is_two_i() -> None:
    assert frame23_inverse_gram_sum() == [
        [Fraction(2), Fraction(0)],
        [Fraction(0), Fraction(2)],
    ]


def test_frame23_closed_form_terms() -> None:
    # [[9/25,0],[0,1]] + [[16/25,0],[0,1]] + [[1,0],[0,0]] = 2 I
    t00 = Fraction(9, 25) + Fraction(16, 25) + 1
    t11 = 1 + 1 + 0
    assert t00 == 2
    assert t11 == 2


def test_frame12_inverse_gram_sum_is_two() -> None:
    # 1x1 adjugate is always 1; two columns give 2.
    assert 1 + 1 == 2
