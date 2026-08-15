"""Independent CPQR census for the Milestone E discovery witnesses."""

from __future__ import annotations

from fractions import Fraction
from structselect.cpqr import cpqr_set, op_norm_2x2_inverse, residual_sq


def frame23():
    return [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]


def frame12():
    return [[Fraction(3, 5), Fraction(4, 5)]]


def test_frame23_empty_residuals_are_leverages() -> None:
    A = frame23()
    assert residual_sq(A, [], 0) == 1
    assert residual_sq(A, [], 1) == Fraction(9, 25)
    assert residual_sq(A, [], 2) == Fraction(16, 25)


def test_frame23_cpqr_selects_0_and_2() -> None:
    assert cpqr_set(frame23()) == [0, 2]


def test_frame12_cpqr_selects_larger_column() -> None:
    assert cpqr_set(frame12()) == [1]


def test_frame23_r_cpqr_is_five_eighths() -> None:
    A = frame23()
    J = cpqr_set(A)
    AJ = [[A[0][J[0]], A[0][J[1]]], [A[1][J[0]], A[1][J[1]]]]
    inv_op = op_norm_2x2_inverse(AJ)
    # ‖A_J⁻¹‖₂ = 5/4, √(k(n-k+1)) = 2, ratio = 5/8
    assert inv_op == Fraction(5, 4)
    assert 2 * (3 - 2 + 1) == 4
    assert inv_op / 2 == Fraction(5, 8)


def test_frame23_second_residuals() -> None:
    A = frame23()
    assert residual_sq(A, [0], 1) == Fraction(9, 25)
    assert residual_sq(A, [0], 2) == Fraction(16, 25)
