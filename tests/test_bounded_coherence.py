"""Exact rational checks for the 19/20 coherence comparison.

These comparisons are the numerical steps in the phase AH argument:
the filler ratio at ε = 45/6400, the leading ratio at m = 20, the
squared leading–filler comparison, and (37/10)^2 < 14. They are not a
theorem and they do not run CPQR.
"""

from fractions import Fraction as F


def test_filler_ratio_below_nineteen_twentieths():
    assert F(83830, 88970) < F(19, 20)


def test_leading_ratio_below_nineteen_twentieths():
    assert F(1, 2) + F(1, 20) <= F(19, 20)


def test_leading_filler_square_below_nineteen_twentieths():
    left = (F(63, 74) + F(45, 6400)) ** 2
    right = (F(19, 20) ** 2) * F(6355, 6400)
    assert left < right


def test_thirty_seven_tenths_squared_below_fourteen():
    assert (F(37, 10) ** 2) < 14
