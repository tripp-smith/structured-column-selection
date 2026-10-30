"""Exact rational check of the length-2 CPQR Rayleigh coefficient.

On the 2×2 identity, CPQR returns both columns and `‖A_J x‖² = ‖x‖²`
for `x = (1, 0)`. The coefficient `k (1 - ρ²) / (2 τ² n)` equals `1/2`
at `τ = 1`, `ρ = 0`, `k = 2`, `n = 2`, and `1/2 * ‖x‖² ≤ ‖A_J x‖²`.
This check is not the theorem.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, matmul, selected_cols


def coefficient(tau, rho, k, n):
    return k * (1 - rho**2) / (F(2) * tau**2 * n)


def test_identity_prefix_rayleigh_coefficient():
    identity = [[F(1), F(0)], [F(0), F(1)]]
    chosen = cpqr_set(identity, k=2)
    assert chosen == [0, 1]
    x = [[F(1)], [F(0)]]
    image = matmul(selected_cols(identity, chosen), x)
    energy_x = x[0][0] ** 2 + x[1][0] ** 2
    energy_image = image[0][0] ** 2 + image[1][0] ** 2
    assert energy_image == energy_x
    coeff = coefficient(F(1), F(0), F(2), F(2))
    assert coeff == F(1, 2)
    assert coeff * energy_x <= energy_image
