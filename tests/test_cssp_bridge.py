"""Exact rank-1 check of the SPEC §11 coefficient identity.

This is behavior evidence for one matrix. It is not the Lean theorem.
"""

from fractions import Fraction as F


def matmul(a, b):
    return [
        [sum(a[i][t] * b[t][j] for t in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def transpose(a):
    return [[a[i][j] for i in range(len(a))] for j in range(len(a[0]))]


def matsub(a, b):
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def cols(a, js):
    return [[a[i][j] for j in js] for i in range(len(a))]


def rows(a, js):
    return [a[j] for j in js]


def frob_sq(a):
    return sum(x * x for row in a for x in row)


def test_rank_one_residual_identity_and_squared_frobenius_comparison():
    q = [[F(1)], [F(0)]]
    assert matmul(transpose(q), q) == [[F(1)]]
    u = [[F(1)]]
    s = [[F(1)]]
    b = matmul(matmul(u, s), transpose(q))
    e = [[F(1), F(1)]]
    a = [[b[0][0] + e[0][0], b[0][1] + e[0][1]]]
    assert a == [[F(2), F(1)]]
    js = [0]
    qj = rows(q, js)
    assert qj == [[F(1)]]
    t = matmul([[F(1)]], transpose(q))
    assert t == [[F(1), F(0)]]
    residual_a = matsub(a, matmul(cols(a, js), t))
    residual_e = matsub(e, matmul(cols(e, js), t))
    assert residual_a == residual_e == [[F(0), F(1)]]
    inv_scale = F(1)
    assert frob_sq(residual_a) <= (1 + inv_scale) ** 2 * frob_sq(e)
    assert frob_sq(residual_a) == F(1)
    assert frob_sq(e) == F(2)
