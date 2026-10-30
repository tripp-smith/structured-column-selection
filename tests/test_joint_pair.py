"""Exact rational checks for the two-column inverse-trace constant.

The 2×2 identity and the equiangular parameters ℓ = 2/3, c = ±1/3 meet
the displayed bound. These checks are not a theorem and they do not run
CPQR.
"""

from fractions import Fraction as F


def inv_trace(ell_i, c, ell_j):
    det = ell_i * ell_j - c * c
    return (ell_i + ell_j) / det


def formula(tau, rho, k, n):
    return F(2) * tau**2 * n / (k * (1 - rho**2))


def test_identity_matches_formula():
    trace = inv_trace(F(1), F(0), F(1))
    assert trace == 2
    assert trace == formula(F(1), F(0), F(2), F(2))


def test_equiangular_pair_matches_formula():
    ell = F(2, 3)
    c = F(1, 3)
    det = ell * ell - c * c
    assert det == F(1, 3)
    assert inv_trace(ell, c, ell) == 4
    assert inv_trace(ell, -c, ell) == 4
    assert formula(F(1), F(1, 2), F(2), F(3)) == 4
