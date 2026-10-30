"""Rational check of the tight majorant at n = k + 2 and τ = 1, ρ = 0.

This rational check is not the theorem. It bounds the majorant at
n = k + 2. It is not itself a CPQR inverse trace. It does not close
outcome 3. The n = 2k majorant is a different statement and is not
polynomial.
"""

from fractions import Fraction as F


def joint_trace_bound_tight_codim_two(k, t):
    """Recurrence M at n = k + 2, τ = 1, ρ = 0."""
    if t < 2:
        raise ValueError("t starts at 2")
    if t == 2:
        return F(2) * (k + 2) / k
    bound = joint_trace_bound_tight_codim_two(k, t - 1)
    return (1 + (F(k) / (k + 2)) * bound) * (
        F((k + 2) - (t - 1)) / (k - (t - 1))
    )


def closed_bound(k):
    """(k - 1) * (k + 2) + (k - 1) * k * (k + 1) / 6 - 1 at ρ = 0."""
    return (k - 1) * (k + 2) + (k - 1) * k * (k + 1) / F(6) - 1


def test_k2_value_equals_bound():
    value = joint_trace_bound_tight_codim_two(2, 2)
    assert value == 4
    assert closed_bound(2) == 4


def test_k3_value_is_nine_bound_thirteen():
    assert joint_trace_bound_tight_codim_two(3, 2) == F(10, 3)
    value = joint_trace_bound_tight_codim_two(3, 3)
    assert value == 9
    assert closed_bound(3) == 13


def test_k4_value_is_fifteen_bound_twentyseven():
    assert joint_trace_bound_tight_codim_two(4, 2) == 3
    assert joint_trace_bound_tight_codim_two(4, 3) == 6
    value = joint_trace_bound_tight_codim_two(4, 4)
    assert value == 15
    assert closed_bound(4) == 27
