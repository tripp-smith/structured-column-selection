import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.PrincipalColumns
import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.ResidualEnergy
import StructuredColumnSelection.CPQRVolume
import StructuredColumnSelection.PrefixInverse
import StructuredColumnSelection.TriangularBound

namespace StructuredColumnSelection

open Classical
open Matrix Finset

/-- Milestone A theorem: transpose correspondence of orthogonality structure. -/
theorem milestoneA_transpose_correspondence {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) :
    OrthogonalRows (Qᵀ) ↔ OrthogonalColumns Q :=
  orthogonalRows_transpose_iff Q

/-- Milestone A helper: selected-column square is definitionally a submatrix. -/
theorem milestoneA_selectedSquare_entry {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) (i j : Fin k) :
    SelectedSquare A J i j = A i (J j) :=
  selectedSquare_apply A J i j

/-- Milestone A helper: selected Gram matrix matches the product form. -/
theorem milestoneA_selectedGram_formula {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) :
    SelectedGram A J = SelectedSquare A J * ((SelectedSquare A J)ᵀ) :=
  selectedGram_eq A J

/-- Milestone B: size-`k` volume weights of an orthogonal-row matrix sum to `1`. -/
theorem milestoneB_volume_normalization {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeight A J = 1 :=
  volumeWeights_sum_eq_one A hA

/-- Finite Cauchy–Binet identity used by Milestone B. -/
theorem milestoneB_cauchyBinet {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ S : { s : Finset (Fin n) // s.card = k },
        (colsSubmatrix A S.1 S.2).det * (rowsSubmatrix B S.1 S.2).det :=
  det_mul_cauchyBinet A B

/-- Milestone C: the finite inverse-Gram identity, via adjugates. -/
theorem milestoneC_inverse_gram_expectation {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      ((n + 1 - k : ℕ) : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) :=
  inverseGramExpectation A hA

/-- Milestone C helper: the same identity without orthogonality. -/
theorem milestoneC_adjugate_sum {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      ((n + 1 - k : ℕ) : R) • Matrix.adjugate (A * Aᵀ) :=
  volumeWeightedInvGrams_sum A

/-- Milestone D: volume-weighted inverse-Frobenius energy is `k(n-k+1)`. -/
theorem milestoneD_expected_inv_frob_sq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, invFrobWeight A J =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  expectedInvFrobSq A hA

/-- Milestone D: finite Markov tail for the inverse-Frobenius proxy. -/
theorem milestoneD_markov_inv_frob {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (invFrobExceeds A
          (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J ≤ δ :=
  markovInvFrob A hA hδ

/-- Milestone E helper: empty-set residuals are column Euclidean energies. -/
theorem milestoneE_residual_empty {k n : ℕ} {R : Type*}
    [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R]
    (A : Matrix (Fin k) (Fin n) R) (j : Fin n) :
    residualSq A ∅ j = ∑ i, A i j ^ 2 :=
  residualSq_empty A j

/-- Milestone E helper: CPQR returns at most `k` columns. -/
theorem milestoneE_cpqr_card_le {k n : ℕ} {R : Type*}
    [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R]
    (A : Matrix (Fin k) (Fin n) R) :
    (cpqrSet A).card ≤ k :=
  cpqrSet_card_le A

/-- Milestone E: empty residuals are leverage scores and sum to `k`. -/
theorem milestoneE_leverage_sum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ j, residualSq A ∅ j = (k : ℝ) :=
  leverageSum A hA

/-- Milestone E: a first CPQR pivot maximises empty residual. -/
theorem milestoneE_first_pivot_is_max {k n : ℕ} {R : Type*}
    [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R]
    (A : Matrix (Fin k) (Fin n) R) {j : Fin n}
    (hj : cpqrPivot A ∅ = some j) (j' : Fin n) :
    residualSq A ∅ j' ≤ residualSq A ∅ j :=
  firstPivot_is_max A hj j'

/-- Milestone E: orthogonal-row CPQR returns exactly `k` columns. -/
theorem milestoneE_cpqr_card_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (cpqrSet A).card = k :=
  cpqrSet_card_eq A hA

/-- Milestone E: a first CPQR pivot has leverage at least `k / n`. -/
theorem milestoneE_first_leverage_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {j : Fin n} (hj : cpqrPivot A ∅ = some j) :
    (k : ℝ) / n ≤ residualSq A ∅ j :=
  firstLeverage_ge A hA hj

/-- Milestone E, `k = 1` only: CPQR volume is at least `n⁻¹`.

This matches the workshop scale `√n` for a single orthonormal row.
It is not a polynomial inverse-norm bound for general `k`. -/
theorem milestoneE_k1_volume_ge {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (n : ℝ)⁻¹ ≤ volumeWeight A (cpqrSet A) :=
  cpqr_k1_volume_ge A hA

/-- Residual energy on an independent column set.

This is a Gram-projector identity, not a CPQR inverse-norm bound. -/
theorem milestoneE_residual_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ∑ j : Fin n, residualSq A J j = (k : ℝ) - (J.card : ℝ) :=
  residualEnergy A hA J hG

/-- The next unused residual is at least the complementary-rank average. -/
theorem milestoneE_next_residual_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (hcard : J.card < n) :
    ((k : ℝ) - (J.card : ℝ)) / ((n : ℝ) - (J.card : ℝ)) ≤
      maxResidual A J :=
  nextResidual_ge A hA J hG hcard

/-- CPQR volume is at least `1 / C(n,k)`.

This is exponential in `k` when `n ≈ 2k` and is not a polynomial
inverse-norm bound. It does not close Milestone E. -/
theorem milestoneE_cpqr_volume_ge_binomial {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (n.choose k : ℝ)⁻¹ ≤ volumeWeight A (cpqrSet A) :=
  cpqr_volume_ge_binomial A hA

/-- Orthogonal-row matrices are contractions in Euclidean energy.

This is not an inverse-norm bound and does not close Milestone E. -/
theorem milestoneE_mulVec_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (x : Fin n → ℝ) :
    vecEnergy (A.mulVec x) ≤ vecEnergy x :=
  mulVec_energy_le A hA x

/-- Every column of an orthogonal-row matrix has leverage at most `1`.

This is not an inverse-norm bound and does not close Milestone E. -/
theorem milestoneE_col_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (j : Fin n) :
    vecEnergy (fun i => A i j) ≤ 1 :=
  col_energy_le A hA j

/-- Last CPQR residual is at least `1 / (n-k+1)`.

This is not a joint `poly(n,k)` inverse-norm bound and does not
close Milestone E. -/
theorem milestoneE_last_residual_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 0 < k) :
    (1 : ℝ) / ((n : ℝ) - ((k - 1 : ℕ) : ℝ)) ≤
      residualSq A (cpqrIterate A (k - 1))
        (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)) :=
  lastResidual_ge A hA hk

/-- Triangular (Drmač–Gugercin / Gu–Eisenstat style) trace bound for the
pivot-ordered CPQR Gram matrix of an orthogonal-row matrix:
`tr((G')⁻¹) ≤ (n - k + 1) · (4^k + 6k - 1) / 9`.

This is polynomial in `n` but exponential in `k` (it grows like
`n · 4^k / 9`), so it is NOT a joint `poly(n, k)` inverse-norm bound
and does NOT close Milestone E. -/
theorem milestoneE_pivot_gram_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((n : ℝ) - k + 1) * ((4 : ℝ)^k + 6*k - 1) / 9 :=
  pivotGram_inv_trace_le A hA

end StructuredColumnSelection
