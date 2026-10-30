"""Exact rational check of the CPQR trace recurrence.

For the identity with τ = 1 and ρ = 0, jointTraceBound at length 2 is 2.
At k = n = 2 the CPQR inverse trace is 2. At k = n = 3 the bounds are 2
then 5, and the inverse trace is 3, so 3 ≤ 5. At k = n = 4 the bounds are
2, 5, then 11, and the inverse trace is 4, so 4 ≤ 11. Equality of the
trace and the bound is asserted only for the 2×2 identity. This is not
the theorem.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def joint_trace_bound(k, n, tau, rho, t):
    if t <= 1:
        return F(0)
    if t == 2:
        return (2 * tau**2 * n) / (k * (1 - rho**2))
    bound = joint_trace_bound(k, n, tau, rho, t - 1)
    s = t - 1
    return bound + (1 + (tau * k / n) * bound) * ((n - s) / (k - s))


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


def identity(size):
    return [[F(1) if i == j else F(0) for j in range(size)] for i in range(size)]


def test_identity_cpqr_trace_recurrence():
    tau = F(1)
    rho = F(0)
    two = identity(2)
    bound2 = joint_trace_bound(F(2), F(2), tau, rho, 2)
    assert bound2 == 2
    trace2 = gram_inv_trace(two, cpqr_set(two, k=2))
    assert trace2 == 2
    three = identity(3)
    assert joint_trace_bound(F(3), F(3), tau, rho, 2) == 2
    bound3 = joint_trace_bound(F(3), F(3), tau, rho, 3)
    assert bound3 == 5
    trace3 = gram_inv_trace(three, cpqr_set(three, k=3))
    assert trace3 == 3
    assert trace3 <= bound3
    four = identity(4)
    assert joint_trace_bound(F(4), F(4), tau, rho, 2) == 2
    assert joint_trace_bound(F(4), F(4), tau, rho, 3) == 5
    bound4 = joint_trace_bound(F(4), F(4), tau, rho, 4)
    assert bound4 == 11
    trace4 = gram_inv_trace(four, cpqr_set(four, k=4))
    assert trace4 == 4
    assert trace4 <= bound4
