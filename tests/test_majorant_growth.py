"""Rational check of the tight majorant along n = k, τ = 2, ρ = 0.

This rational check is not the theorem. It lower-bounds the majorant only.
It is not a CPQR inverse trace. It does not close outcome 3.
"""

from fractions import Fraction as F


def joint_trace_bound_tight_square_two(k, t):
    """jointTraceBoundTight at n = k, τ = 2, ρ = 0."""
    if t < 2:
        raise ValueError("t starts at 2")
    if t == 2:
        return F(8)
    bound = joint_trace_bound_tight_square_two(k, t - 1)
    return (1 + 2 * bound) * 1


def test_k4_majorant_beats_two_pow():
    assert joint_trace_bound_tight_square_two(4, 2) == 8
    assert joint_trace_bound_tight_square_two(4, 3) == 17
    value = joint_trace_bound_tight_square_two(4, 4)
    assert value == 35
    assert 2**5 == 32
    assert 32 <= value


def test_k6_majorant_at_least_two_pow():
    value = joint_trace_bound_tight_square_two(6, 6)
    assert value >= 2**7
