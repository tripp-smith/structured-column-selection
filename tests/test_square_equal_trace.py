"""Exact rational check of the square equal-leverage CPQR trace bound.

This rational check is not the theorem. The Lean statement is square and
equal-leverage only and does not close outcome 3. Column energies of the
identity are equal, so the leverage ratio is 1, and off-diagonal inner
products are 0, so coherence 0 is admissible.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def square_equal_bound(k, rho=F(0)):
    return F(k) - 2 + F(2) / (1 - rho**2)


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


def test_identity_k3_square_equal_trace():
    chosen = cpqr_set(identity(3), k=3)
    trace = gram_inv_trace(identity(3), chosen)
    bound = square_equal_bound(3)
    assert bound == 3
    assert trace == 3


def test_identity_k4_square_equal_trace():
    chosen = cpqr_set(identity(4), k=4)
    trace = gram_inv_trace(identity(4), chosen)
    bound = square_equal_bound(4)
    assert bound == 4
    assert trace == 4
