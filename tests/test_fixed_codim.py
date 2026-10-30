"""Rational check of the tight majorant at n = k + r and τ = 1, ρ = 0.

This rational check is not the theorem. The bound is uniform in r and
looser than the phase-AW and phase-AX bounds. It does not close
outcome 3. It is not a joint polynomial in n and k.
"""

from fractions import Fraction as F
from math import factorial


def joint_trace_bound_tight_fixed_codim(k, r, t):
    """Recurrence M at n = k + r, τ = 1, ρ = 0."""
    if t < 2:
        raise ValueError("t starts at 2")
    if t == 2:
        return F(2) * (k + r) / k
    bound = joint_trace_bound_tight_fixed_codim(k, r, t - 1)
    return (1 + (F(k) / (k + r)) * bound) * (
        F((k + r) - (t - 1)) / (k - (t - 1))
    )


def closed_bound(k, r):
    """(2 (k + r)^(r + 1) + k (k + r)^r) / r! at ρ = 0."""
    return (2 * (k + r) ** (r + 1) + k * (k + r) ** r) / F(factorial(r))


def test_r1_k2_value_three():
    value = joint_trace_bound_tight_fixed_codim(2, 1, 2)
    assert value == 3
    assert value <= closed_bound(2, 1)


def test_r1_k3_value_at_most_bound():
    value = joint_trace_bound_tight_fixed_codim(3, 1, 3)
    assert value <= closed_bound(3, 1)


def test_r2_k2_value_four():
    value = joint_trace_bound_tight_fixed_codim(2, 2, 2)
    assert value == 4
    assert value <= closed_bound(2, 2)


def test_r2_k4_value_fifteen():
    value = joint_trace_bound_tight_fixed_codim(4, 2, 4)
    assert value == 15
    assert value <= closed_bound(4, 2)


def test_r3_k3_value_at_most_bound():
    value = joint_trace_bound_tight_fixed_codim(3, 3, 3)
    assert value <= closed_bound(3, 3)
