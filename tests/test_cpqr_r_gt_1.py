"""Independent exact certification of the r_CPQR > 1 witness (C=1 case).

The witness in ``experiments/cpqr_r_gt_1_witness_3_8.json`` is a rational
``3×8`` orthogonal-row matrix. CPQR selects ``{0, 1, 2}`` and the selected
block has a singular value below ``1/√18``, so ``‖A_J⁻¹‖₂ > √(k(n-k+1))``.

This kills only the ideal ``C = 1`` workshop-scale bound. The certified
inverse norm (≈ 4.38) is far below the campaign's named polynomial
``max(n³, k³, (k(n-k+1))²) = 512``, so Milestone E stays OPEN. These
tests assert only the certificate facts, never a universal bound.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from structselect.cpqr import cpqr_set, matmul, residual_sq, transpose

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "experiments" / "cpqr_r_gt_1_witness_3_8.json"


def _load() -> tuple[list[list[Fraction]], list[Fraction], dict]:
    rec = json.loads(RECORD.read_text())
    A = [[Fraction(v) for v in row] for row in rec["witness_Q"]]
    x = [Fraction(v) for v in rec["test_vector_Q"]]
    return A, x, rec


def test_witness_is_row_orthonormal_exactly() -> None:
    A, _, _ = _load()
    AAT = matmul(A, transpose(A))
    for i in range(3):
        for j in range(3):
            assert AAT[i][j] == (1 if i == j else 0)


def test_witness_cpqr_selects_first_three_columns() -> None:
    A, _, _ = _load()
    assert cpqr_set(A) == [0, 1, 2]


def test_witness_pivot_margins_strictly_positive() -> None:
    """Every step has a unique maximizer: no tie-break ambiguity."""
    A, _, _ = _load()
    chosen: list[int] = []
    for _ in range(3):
        unused = [j for j in range(8) if j not in chosen]
        res = {j: residual_sq(A, chosen, j) for j in unused}
        best_j = min(j for j in unused if res[j] == max(res.values()))
        assert all(res[best_j] > res[j] for j in unused if j != best_j)
        assert best_j == len(chosen)
        chosen.append(best_j)


def test_witness_inverse_norm_lower_bound() -> None:
    """18·‖A_J x‖² < ‖x‖² certifies σ_min² < 1/18, i.e. r_CPQR > 1."""
    A, x, rec = _load()
    AJ = [[A[i][j] for j in (0, 1, 2)] for i in range(3)]
    AJx = [sum(AJ[i][p] * x[p] for p in range(3)) for i in range(3)]
    lhs = 18 * sum(v * v for v in AJx)
    rhs = sum(v * v for v in x)
    assert lhs < rhs
    # The recorded certified lower bound is r > 1.03; stay conservative.
    assert float(rhs / lhs) * 18 > 18.0
    assert rec["certificate"]["r_lb"] > 1


def test_witness_stays_below_named_polynomial() -> None:
    """The certified instance is polynomial-scale: E remains OPEN."""
    _, _, rec = _load()
    inv_lb = rec["certificate"]["inv_lb"]
    named_poly = max(8**3, 3**3, (3 * (8 - 3 + 1)) ** 2)
    assert named_poly == 512
    assert inv_lb < named_poly
