"""Independent enumeration of volume weights for Milestone B witnesses."""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


def det2(a00: Fraction, a01: Fraction, a10: Fraction, a11: Fraction) -> Fraction:
    return a00 * a11 - a01 * a10


def volume_weight_sum_frame23() -> Fraction:
    # A = [[1, 0, 0], [0, 3/5, 4/5]]
    A = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]
    total = Fraction(0)
    for j0, j1 in combinations(range(3), 2):
        total += det2(A[0][j0], A[0][j1], A[1][j0], A[1][j1]) ** 2
    return total


def volume_weight_sum_frame12() -> Fraction:
    A = [Fraction(3, 5), Fraction(4, 5)]
    return A[0] ** 2 + A[1] ** 2


def test_frame23_volume_sum_is_one() -> None:
    assert volume_weight_sum_frame23() == 1


def test_frame12_volume_sum_is_one() -> None:
    assert volume_weight_sum_frame12() == 1


def test_frame23_closed_form_terms() -> None:
    assert (Fraction(3, 5) ** 2) + (Fraction(4, 5) ** 2) + 0 == 1
