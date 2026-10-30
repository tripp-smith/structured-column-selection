"""Rational check of the tight majorant along n = 2k, τ = 1, ρ = 0.

This rational check is not the theorem. It lower-bounds the majorant only.
It is not a CPQR inverse trace. It does not close outcome 3. The square
τ = 1 regime is a different statement.
"""

from fractions import Fraction as F


def joint_trace_bound_tight_equal_rect(k, t):
    """jointTraceBoundTight at n = 2k, τ = 1, ρ = 0."""
    if t < 2:
        raise ValueError("t starts at 2")
    n = 2 * k
    if t == 2:
        return F(2) * n / k
    bound = joint_trace_bound_tight_equal_rect(k, t - 1)
    return (1 + (F(k) / n) * bound) * (F(n - (t - 1)) / (k - (t - 1)))


def test_k2_majorant_reaches_four():
    value = joint_trace_bound_tight_equal_rect(2, 2)
    assert value == 4
    assert F(2) ** 2 / 2 <= 4


def test_k4_majorant_reaches_55_over_2():
    assert joint_trace_bound_tight_equal_rect(4, 2) == 4
    assert joint_trace_bound_tight_equal_rect(4, 3) == 9
    value = joint_trace_bound_tight_equal_rect(4, 4)
    assert value == F(55, 2)
    assert F(2) ** 4 / 4 <= F(55, 2)
