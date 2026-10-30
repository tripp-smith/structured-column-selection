"""Rational check of the tight majorant at n = k + 1 and τ = 1, ρ = 0.

This rational check is not the theorem. It bounds the majorant at
n = k + 1. It is not a CPQR inverse trace by itself. It does not close
outcome 3. The n = 2k majorant is a different statement and is not
polynomial.
"""

from fractions import Fraction as F


def joint_trace_bound_tight_codim_one(k, t):
    """Recurrence M at n = k + 1, τ = 1, ρ = 0."""
    if t < 2:
        raise ValueError("t starts at 2")
    if t == 2:
        return F(2) * (k + 1) / k
    bound = joint_trace_bound_tight_codim_one(k, t - 1)
    return (1 + (F(k) / (k + 1)) * bound) * (
        F((k + 1) - (t - 1)) / (k - (t - 1))
    )


def closed_bound(k):
    """(k + 1) * (k + 2) + 2 * k, the ρ = 0 case of the closed bound."""
    return (k + 1) * (k + 2) + 2 * k


def test_k2_recurrence_is_three():
    value = joint_trace_bound_tight_codim_one(2, 2)
    assert value == 3
    assert closed_bound(2) == 16
    assert value <= 16


def test_k3_recurrence_reaches_six():
    assert joint_trace_bound_tight_codim_one(3, 2) == F(8, 3)
    value = joint_trace_bound_tight_codim_one(3, 3)
    assert value == 6
    assert closed_bound(3) == 26
    assert value <= 26


def test_k4_value_at_most_38():
    value = joint_trace_bound_tight_codim_one(4, 4)
    assert closed_bound(4) == 5 * 6 + 8
    assert value <= closed_bound(4)
