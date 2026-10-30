"""Exact rational check of the joint three-row CPQR set.

On the 3×3 identity, CPQR returns three columns and the Gram inverse
trace is 3. The bound at τ = 1, ρ = 0, n = 3 equals 5, and for
x = (1, 0, 0) one has ‖x‖² ≤ 5 ‖A_J x‖². This check does not assert
that the trace equals 5. It is not the theorem.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def bound(tau, rho, n):
    return F(2) * tau**2 * n / (F(3) * (1 - rho**2)) + (
        1 + F(2) * tau**3 / (1 - rho**2)
    ) * (n - 2)


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


def gram_inv_trace(A, indices):
    columns = selected_cols(A, indices)
    gram = matmul(transpose(columns), columns)
    return cofactor_trace(gram) / det(gram)


def test_identity_three_row_cpqr_set():
    identity = [
        [F(1), F(0), F(0)],
        [F(0), F(1), F(0)],
        [F(0), F(0), F(1)],
    ]
    chosen = cpqr_set(identity, k=3)
    assert len(chosen) == 3
    trace = gram_inv_trace(identity, chosen)
    assert trace == 3
    value = bound(F(1), F(0), F(3))
    assert value == 5
    x = [[F(1)], [F(0)], [F(0)]]
    image = matmul(selected_cols(identity, chosen), x)
    energy_x = sum(row[0] ** 2 for row in x)
    energy_image = sum(row[0] ** 2 for row in image)
    assert energy_x <= value * energy_image
