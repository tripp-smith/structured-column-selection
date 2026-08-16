"""SPEC §9 rational certificate automation: Cayley / Givens / frame38.

These tests prove exact ``AAᵀ = I``, unique CPQR pivots, and the
inverse-norm inequality on concrete witnesses. They do not assert a
universal CPQR bound. A ``C = 1`` certificate leaves Milestone E OPEN
unless the inverse-norm lower bound exceeds the named polynomial.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np

from structselect.certify import (
    cayley,
    cayley_stiefel,
    certify,
    certify_json_record,
    circle_point_from_half_tan,
    inverse_cayley,
    is_row_orthonormal,
    is_skew_symmetric,
    lean_rat,
    matrix_q,
    nearest_pythagorean,
    pythagorean_cs,
    reparametrize_cayley,
    reparametrize_givens,
    skew_from_upper,
)
from structselect.cpqr import cpqr_set, matmul, transpose

ROOT = Path(__file__).resolve().parent.parent
FRAME38 = ROOT / "experiments" / "cpqr_r_gt_1_witness_3_8.json"


def _frame38() -> tuple[list[list[Fraction]], list[Fraction], dict]:
    rec = json.loads(FRAME38.read_text())
    A = [[Fraction(v) for v in row] for row in rec["witness_Q"]]
    x = [Fraction(v) for v in rec["test_vector_Q"]]
    return A, x, rec


def _frame23() -> list[list[Fraction]]:
    return [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]


def test_cayley_2d_is_three_four_five() -> None:
    """Half-tan ``t = 1/2`` is the Pythagorean triple ``(3,4,5)``."""
    c, s = circle_point_from_half_tan(Fraction(1, 2))
    assert (c, s) == (Fraction(3, 5), Fraction(4, 5))
    assert c * c + s * s == 1
    c2, s2 = pythagorean_cs(2, 1)
    assert (c2, s2) == (Fraction(3, 5), Fraction(4, 5))


def test_cayley_of_skew_is_orthogonal() -> None:
    S = skew_from_upper(3, [Fraction(1, 2), Fraction(-1, 3), Fraction(1, 7)])
    assert is_skew_symmetric(S)
    Q = cayley(S)
    QTQ = matmul(transpose(Q), Q)
    for i in range(3):
        for j in range(3):
            assert QTQ[i][j] == (1 if i == j else 0)
    S_back = inverse_cayley(Q)
    for i in range(3):
        for j in range(3):
            assert S_back[i][j] == S[i][j]


def test_cayley_stiefel_rows_are_orthonormal() -> None:
    S = skew_from_upper(4, [Fraction(1, 5)] * 6)
    A = cayley_stiefel(S, 2)
    assert is_row_orthonormal(A)
    assert len(A) == 2 and len(A[0]) == 4


def test_nearest_pythagorean_recovers_three_four_five() -> None:
    c, s = nearest_pythagorean(0.6, 0.8, max_den=10)
    assert (c, s) == (Fraction(3, 5), Fraction(4, 5))


def test_givens_reparam_recovers_frame23() -> None:
    A_num = np.array(_frame23(), dtype=float)
    A_q = reparametrize_givens(A_num, max_den=10)
    assert is_row_orthonormal(A_q)
    assert A_q == _frame23()
    assert cpqr_set(A_q) == [0, 2]


def test_frame38_exact_recertifies() -> None:
    """The published 3×8 witness still satisfies all three SPEC §9 checks."""
    A, x, rec = _frame38()
    cert = certify(
        A,
        test_vector=x,
        reparametrize_method="exact",
        note=rec["note"],
    )
    assert cert.ok
    assert cert.method == "exact"
    assert is_row_orthonormal(cert.A)
    assert cert.J == [0, 1, 2]
    assert cert.trajectory == [0, 1, 2]
    assert cert.min_margin > 0
    assert all(m > 0 for _s, _p, m in cert.margins)
    lhs = cert.c * sum(
        v * v
        for v in [
            sum(cert.A[i][j] * x[p] for p, j in enumerate(cert.trajectory))
            for i in range(3)
        ]
    )
    rhs = sum(v * v for v in x)
    assert lhs < rhs
    assert cert.c == 18
    assert cert.r_lb > 1
    assert cert.inv_lb < 512
    assert cert.below_named_poly
    rec_margin = Fraction(rec["certificate"]["min_margin"])
    assert cert.min_margin == rec_margin


def test_frame38_json_helper_recertifies() -> None:
    cert = certify_json_record(FRAME38)
    assert cert.ok
    assert cert.r_lb > 1
    assert cert.inv_lb < cert.named_poly


def test_frame38_cayley_recertifies() -> None:
    """Float frame38 → Cayley(D=10⁴) still certifies AAᵀ=I, pivots, r>1.

    The recovered matrix need not equal the published fractions (the
    orthogonal completion is not unique), but SPEC §9 must still pass.
    """
    A, _x, _rec = _frame38()
    A_num = np.array([[float(v) for v in row] for row in A], dtype=float)
    cert = certify(
        A_num,
        reparametrize_method="cayley",
        denominator=10_000,
        tag="D=10000-recertify",
    )
    assert is_row_orthonormal(cert.A)
    assert cert.ok, cert.failures
    assert cert.method == "cayley"
    assert cert.min_margin > 0
    assert cert.r_lb > 1
    assert cert.inv_lb < 512
    assert cert.below_named_poly
    err = max(
        abs(float(cert.A[i][j]) - float(A[i][j]))
        for i in range(3)
        for j in range(8)
    )
    assert err < 5e-3


def test_frame23_exact_certificate_and_lean_snippet() -> None:
    cert = certify(_frame23(), reparametrize_method="exact")
    assert cert.ok
    assert cert.J == [0, 2]
    assert cert.trajectory[0] == 0
    snippet = cert.lean_snippets("frame23auto")
    assert "native_decide" in snippet
    assert "frame23auto_mul_transpose" in snippet
    assert "frame23auto_cpqr_set" in snippet
    assert "frame23auto_inv_norm_lb" in snippet
    assert lean_rat(Fraction(-3, 5)).startswith("(-")
    assert "Milestone E remains OPEN" in snippet


def test_certificate_json_roundtrip_schema() -> None:
    cert = certify(_frame23(), reparametrize_method="exact")
    obj = json.loads(cert.to_json())
    assert obj["certificate"]["ok"] is True
    assert "witness_Q" in obj and "test_vector_Q" in obj
    assert obj["certificate"]["below_named_poly"] is True


def test_synthetic_cayley_frame_certifies_orthonormality() -> None:
    S = skew_from_upper(
        4,
        [Fraction(1, 4), Fraction(0), Fraction(-1, 5), Fraction(1, 3), Fraction(0), Fraction(2, 7)],
    )
    A = cayley_stiefel(S, 2)
    cert = certify(A, reparametrize_method="exact")
    assert is_row_orthonormal(cert.A)
    assert cert.min_margin > 0
    assert cert.ok
    assert cert.below_named_poly


def test_free_generator_cayley_makes_exact_parseval() -> None:
    rng = np.random.default_rng(0)
    B = rng.standard_normal((2, 5))
    A = reparametrize_cayley(B, denominator=50)
    assert is_row_orthonormal(A)
    cert = certify(A, reparametrize_method="exact")
    assert cert.ok
    assert cert.k == 2 and cert.n == 5


def test_exact_mode_rejects_non_orthonormal() -> None:
    A = matrix_q([[1, 1, 0], [0, 1, 1]])
    cert = certify(A, reparametrize_method="exact")
    assert not cert.ok
    assert "AAᵀ ≠ I" in cert.failures


def test_numeric_4x12_cayley_is_parseval_but_not_r_gt_1() -> None:
    """Cayley rounding of the 4×12 float record is exact Parseval, not r>1.

    The numeric observation stays uncertified. Even a future r>1
    certificate at 4×12 would sit below the named polynomial 1728, so
    Milestone E would remain OPEN.
    """
    rec = json.loads(
        (ROOT / "experiments" / "cpqr_r_gt_1_numeric_4_12.json").read_text()
    )
    A_num = np.array(rec["matrix"], dtype=float)
    cert = certify(A_num, reparametrize_method="cayley", denominator=1000)
    assert is_row_orthonormal(cert.A)
    assert cert.min_margin > 0
    assert cert.r_lb < 1
    assert cert.inv_lb < cert.named_poly
    assert cert.named_poly == max(12**3, 4**3, (4 * (12 - 4 + 1)) ** 2)


def test_c1_witness_does_not_close_e() -> None:
    """Guard: even a passing r>1 certificate stays below the named polynomial."""
    cert = certify_json_record(FRAME38)
    named = max(8**3, 3**3, (3 * (8 - 3 + 1)) ** 2)
    assert named == 512
    assert cert.named_poly == named
    assert cert.inv_lb < named
    assert cert.r_lb > 1
    assert "OPEN" in cert.note or cert.below_named_poly
