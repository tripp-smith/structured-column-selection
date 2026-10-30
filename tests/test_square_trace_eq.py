"""Rational check that a square orthogonal-row CPQR Gram has inverse trace k.

This rational check is not the theorem. Square only. Does not close outcome 3.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def cofactor_trace(gram):
    size = len(gram)
    total = F(0)
    for i in range(size):
        minor = [
            [gram[r][c] for c in range(size) if c != i]
            for r in range(size)
            if r != i
        ]
        sign = F(1) if (i + i) % 2 == 0 else F(-1)
        total += sign * det(minor)
    return total


def gram_of(A, indices):
    columns = selected_cols(A, indices)
    return matmul(transpose(columns), columns)


def gram_inv_trace(A, indices):
    gram = gram_of(A, indices)
    return cofactor_trace(gram) / det(gram)


def identity(k):
    return [[F(1) if i == j else F(0) for j in range(k)] for i in range(k)]


def row_dot(A, i, j):
    return sum(A[i][c] * A[j][c] for c in range(len(A[0])))


def col_dot(A, i, j):
    return sum(A[r][i] * A[r][j] for r in range(len(A)))


def test_identity_k2_square_trace_eq():
    A = identity(2)
    chosen = cpqr_set(A, k=2)
    assert len(chosen) == 2
    assert gram_inv_trace(A, chosen) == 2


def test_identity_k3_square_trace_eq():
    A = identity(3)
    chosen = cpqr_set(A, k=3)
    assert len(chosen) == 3
    assert gram_inv_trace(A, chosen) == 3


def test_rotation_square_trace_eq():
    A = [
        [F(3, 5), F(-4, 5)],
        [F(4, 5), F(3, 5)],
    ]
    assert row_dot(A, 0, 0) == 1
    assert row_dot(A, 1, 1) == 1
    assert row_dot(A, 0, 1) == 0
    assert col_dot(A, 0, 1) == 0
    chosen = cpqr_set(A, k=2)
    assert len(chosen) == 2
    assert gram_inv_trace(A, chosen) == 2
