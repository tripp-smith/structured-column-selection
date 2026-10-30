"""Exact rational check of the length-2 CPQR prefix on the 2×2 identity.

CPQR returns both columns, and the inverse trace of that Gram is 2.
That matches `2 τ² n / (k (1 - ρ²))` at τ = 1, ρ = 0, k = 2, n = 2.
This check is not the theorem.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, matmul, selected_cols, transpose


def formula(tau, rho, k, n):
    return F(2) * tau**2 * n / (k * (1 - rho**2))


def gram_inv_trace(A, indices):
    columns = selected_cols(A, indices)
    gram = matmul(transpose(columns), columns)
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    return (gram[0][0] + gram[1][1]) / det


def test_identity_cpqr_prefix_matches_formula():
    identity = [[F(1), F(0)], [F(0), F(1)]]
    chosen = cpqr_set(identity, k=2)
    assert chosen == [0, 1]
    trace = gram_inv_trace(identity, chosen)
    assert trace == 2
    assert trace == formula(F(1), F(0), F(2), F(2))
