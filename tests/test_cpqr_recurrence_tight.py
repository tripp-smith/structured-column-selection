"""Exact rational check of the tight CPQR trace recurrence.

This rational check is not the theorem. The recurrence is not a polynomial.
It does not close outcome 3.

On the square identity, column energies are equal and off-diagonal inner
products are 0, so τ = 1 and ρ = 0 are admissible. At k = n = 3 the tight
bounds are 2 then 3, and the CPQR prefix inverse traces are 2 and 3. The
loose successor at t = 3 is 5, and 3 < 5. At k = n = 4 the tight bounds are
2, 3, 4, and the inverse traces equal those numbers. The loose value at
t = 4 is 11, and 4 < 11.
"""

from fractions import Fraction as F

from structselect.cpqr import (
    cpqr_set,
    det,
    leverage_scores,
    matmul,
    selected_cols,
    transpose,
)


def joint_trace_bound_tight(k, n, tau, rho, t):
    if t <= 1:
        return F(0)
    if t == 2:
        return (2 * tau**2 * n) / (k * (1 - rho**2))
    bound = joint_trace_bound_tight(k, n, tau, rho, t - 1)
    s = t - 1
    return (1 + (tau * k / n) * bound) * ((n - s) / (k - s))


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


def column_dot(A, i, j):
    return sum(row[i] * row[j] for row in A)


def assert_square_identity_hypotheses(A):
    scores = leverage_scores(A)
    assert len(set(scores)) == 1
    n = len(A[0])
    for i in range(n):
        for j in range(n):
            if i != j:
                assert column_dot(A, i, j) == 0


def test_identity_k3_tight_recurrence():
    tau = F(1)
    rho = F(0)
    three = identity(3)
    assert_square_identity_hypotheses(three)
    assert joint_trace_bound_tight(F(3), F(3), tau, rho, 2) == 2
    assert joint_trace_bound_tight(F(3), F(3), tau, rho, 3) == 3
    assert gram_inv_trace(three, cpqr_set(three, k=2)) == 2
    assert gram_inv_trace(three, cpqr_set(three, k=3)) == 3
    loose3 = joint_trace_bound(F(3), F(3), tau, rho, 3)
    assert loose3 == 5
    assert 3 < loose3


def test_identity_k4_tight_recurrence():
    tau = F(1)
    rho = F(0)
    four = identity(4)
    assert_square_identity_hypotheses(four)
    assert joint_trace_bound_tight(F(4), F(4), tau, rho, 2) == 2
    assert joint_trace_bound_tight(F(4), F(4), tau, rho, 3) == 3
    assert joint_trace_bound_tight(F(4), F(4), tau, rho, 4) == 4
    assert gram_inv_trace(four, cpqr_set(four, k=2)) == 2
    assert gram_inv_trace(four, cpqr_set(four, k=3)) == 3
    assert gram_inv_trace(four, cpqr_set(four, k=4)) == 4
    loose4 = joint_trace_bound(F(4), F(4), tau, rho, 4)
    assert loose4 == 11
    assert 4 < loose4
