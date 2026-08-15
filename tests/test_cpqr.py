"""Independent CPQR census for the Milestone E structural layer."""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from structselect.cpqr import (
    cpqr_set,
    first_pivot,
    leverage_scores,
    op_norm_2x2_inverse,
    r_cpqr_2x2,
    residual_sq,
)


def frame23():
    return [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5)],
    ]


def frame12():
    return [[Fraction(3, 5), Fraction(4, 5)]]


def hadamard24():
    h = Fraction(1, 2)
    return [
        [h, h, h, h],
        [h, -h, h, -h],
    ]


def nonuniform24():
    """frame23 padded by a zero column: highly nonuniform leverages."""
    return [
        [Fraction(1), Fraction(0), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(3, 5), Fraction(4, 5), Fraction(0)],
    ]


def identity_pad24():
    return [
        [Fraction(1), Fraction(0), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(1), Fraction(0), Fraction(0)],
    ]


def test_frame23_empty_residuals_are_leverages() -> None:
    A = frame23()
    assert residual_sq(A, [], 0) == 1
    assert residual_sq(A, [], 1) == Fraction(9, 25)
    assert residual_sq(A, [], 2) == Fraction(16, 25)


def test_frame23_leverage_sum_is_k() -> None:
    assert sum(leverage_scores(frame23())) == 2


def test_frame23_first_pivot_is_max() -> None:
    A = frame23()
    j = first_pivot(A)
    assert j == 0
    scores = leverage_scores(A)
    assert all(s <= scores[j] for s in scores)


def test_frame23_cpqr_selects_0_and_2() -> None:
    assert cpqr_set(frame23()) == [0, 2]


def test_frame12_cpqr_selects_larger_column() -> None:
    assert cpqr_set(frame12()) == [1]


def test_orthogonal_frames_have_card_k() -> None:
    assert len(cpqr_set(frame23())) == 2
    assert len(cpqr_set(frame12())) == 1
    assert len(cpqr_set(hadamard24())) == 2
    assert len(cpqr_set(nonuniform24())) == 2
    assert len(cpqr_set(identity_pad24())) == 2


def test_frame23_r_cpqr_is_five_eighths() -> None:
    A = frame23()
    J = cpqr_set(A)
    AJ = [[A[0][J[0]], A[0][J[1]]], [A[1][J[0]], A[1][J[1]]]]
    inv_op = op_norm_2x2_inverse(AJ)
    # ‖A_J⁻¹‖₂ = 5/4, √(k(n-k+1)) = 2, ratio = 5/8
    assert inv_op == Fraction(5, 4)
    assert 2 * (3 - 2 + 1) == 4
    assert inv_op / 2 == Fraction(5, 8)
    assert r_cpqr_2x2(A) == Fraction(5, 8)


def test_frame23_second_residuals() -> None:
    A = frame23()
    assert residual_sq(A, [0], 1) == Fraction(9, 25)
    assert residual_sq(A, [0], 2) == Fraction(16, 25)


def _inv_op_2row(A) -> Fraction:
    J = cpqr_set(A)
    AJ = [[A[0][J[0]], A[0][J[1]]], [A[1][J[0]], A[1][J[1]]]]
    return op_norm_2x2_inverse(AJ)


def test_census_records_r_cpqr_without_a_bound() -> None:
    """Record inverse norms on structured frames. Do not assert a universal bound."""
    records = {
        "frame23": (_inv_op_2row(frame23()), 2 * (3 - 2 + 1)),
        "nonuniform24": (_inv_op_2row(nonuniform24()), 2 * (4 - 2 + 1)),
        "identity_pad24": (_inv_op_2row(identity_pad24()), 2 * (4 - 2 + 1)),
    }
    assert records["frame23"] == (Fraction(5, 4), 4)
    assert records["nonuniform24"] == (Fraction(5, 4), 6)
    assert records["identity_pad24"] == (1, 6)
    assert r_cpqr_2x2(frame23()) == Fraction(5, 8)
    J = cpqr_set(hadamard24())
    AJ = [
        [hadamard24()[0][J[0]], hadamard24()[0][J[1]]],
        [hadamard24()[1][J[0]], hadamard24()[1][J[1]]],
    ]
    detAJ = AJ[0][0] * AJ[1][1] - AJ[0][1] * AJ[1][0]
    assert detAJ != 0
    assert all(inv_op > 0 and bound_sq > 0 for inv_op, bound_sq in records.values())


def _haar_rows(k: int, n: int, rng: np.random.Generator) -> np.ndarray:
    g = rng.standard_normal((n, k))
    q, _ = np.linalg.qr(g)
    return q.T


def _cpqr_float(A: np.ndarray) -> list[int]:
    k, n = A.shape
    chosen: list[int] = []
    unused = set(range(n))
    for _ in range(k):
        scores = {}
        for j in unused:
            B = A[:, chosen] if chosen else np.zeros((k, 0))
            if B.shape[1] == 0:
                scores[j] = float(np.sum(A[:, j] ** 2))
                continue
            G = B.T @ B
            gdet = float(np.linalg.det(G))
            if abs(gdet) < 1e-14:
                scores[j] = 0.0
                continue
            B2 = np.column_stack([B, A[:, j]])
            scores[j] = float(np.linalg.det(B2.T @ B2) / gdet)
        best = max(scores.values())
        if best <= 1e-14:
            break
        j = min(j for j, s in scores.items() if abs(s - best) <= 1e-12)
        chosen.append(j)
        unused.remove(j)
    return sorted(chosen)


def test_haar_census_is_full_rank() -> None:
    rng = np.random.default_rng(0)
    ratios = []
    for k, n in ((2, 5), (2, 8), (3, 7)):
        for _ in range(8):
            A = _haar_rows(k, n, rng)
            J = _cpqr_float(A)
            assert len(J) == k
            inv_op = np.linalg.norm(np.linalg.inv(A[:, J]), 2)
            bound = np.sqrt(k * (n - k + 1))
            ratios.append(inv_op / bound)
    assert all(np.isfinite(r) and r > 0 for r in ratios)
