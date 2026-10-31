"""Rational lower bound on the phase-AY expression at r = k and ρ = 0.

This rational check is not the theorem. It lower-bounds the phase-AY
expression at r = k and ρ = 0. It is not a CPQR inverse trace. It does
not close outcome 3.
"""

from fractions import Fraction
from math import factorial


def bound(k):
    """(2 * (2k)^(k + 1) + k * (2k)^k) / k!."""
    num = 2 * (2 * k) ** (k + 1) + k * (2 * k) ** k
    return Fraction(num, factorial(k))


def test_k4_equals_81920_over_24():
    assert bound(4) == Fraction(81920, 24)
    assert 2 ** 6 <= bound(4)


def test_k6_beats_two_pow_eight():
    assert 2 ** 8 <= bound(6)
