import StructuredColumnSelection.EqualEnergyPivot
import StructuredColumnSelection.WideIncoherent
import StructuredColumnSelection.WideIncoherentEscape
import StructuredColumnSelection.NormalizedCoherence
import StructuredColumnSelection.DesignFrame
import StructuredColumnSelection.SymmetricCompletion
import StructuredColumnSelection.TripleDesign
import StructuredColumnSelection.ScaledDesignFrame
import StructuredColumnSelection.FrameCoherence
import StructuredColumnSelection.LeadingCoherence
import StructuredColumnSelection.BoundedCoherence
import StructuredColumnSelection.JointPairGram
import StructuredColumnSelection.OrthogonalColumns
import StructuredColumnSelection.ZeroCoeffPivot
import StructuredColumnSelection.PivotSplit
import StructuredColumnSelection.LeverageRatioSplit
import StructuredColumnSelection.OrthogonalBlockPivot
import StructuredColumnSelection.EqualEnergyBlockSplit
import StructuredColumnSelection.EqualEnergyThirdPivot
import StructuredColumnSelection.IncrementSet
import StructuredColumnSelection.InvSpectralBound
import StructuredColumnSelection.InvTraceInduction
import StructuredColumnSelection.InvTraceGrowth
import StructuredColumnSelection.BestColumnIncrement
import StructuredColumnSelection.InvTraceStep
import StructuredColumnSelection.CSSPBridge
import StructuredColumnSelection.WideLeverage
import StructuredColumnSelection.WideCPQR
import StructuredColumnSelection.WideCPQRParameters
import StructuredColumnSelection.WideCPQRGrowth
import StructuredColumnSelection.VolumeSampling
import StructuredColumnSelection.ActualInverseExpectation
import StructuredColumnSelection.ColumnBudget
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
import StructuredColumnSelection.ResidualMono
import StructuredColumnSelection.SigmaMinBounds
import StructuredColumnSelection.RowOrthoConstraints
import StructuredColumnSelection.StaticClass

namespace StructuredColumnSelection

open Classical
open Matrix Finset
open scoped Matrix

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

/-- Residual is antitone in the independent index set.

This is a projector identity, not a CPQR inverse-norm bound, and
does not close Milestone E. -/
theorem milestoneE_residual_antitone {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J J' : Finset (Fin n)}
    (hJJ : J ⊆ J') (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A J').det ≠ 0) (j : Fin n) :
    residualSq A J' j ≤ residualSq A J j :=
  residualSq_antitone A hJJ hG hG' j

/-- Rank-1 residual downdate after inserting an independent column.

This is not a CPQR inverse-norm bound and does not close Milestone E. -/
theorem milestoneE_residual_insert_downdate {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {p : Fin n}
    (hp : p ∉ J) (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A (insert p J)).det ≠ 0) (j : Fin n) :
    residualSq A (insert p J) j =
      residualSq A J j -
        (((fun i => A i j) ⬝ᵥ residualVec A J p) ^ 2) *
          (residualSq A J p)⁻¹ :=
  residualSq_insert_downdate A hp hG hG' j

/-- Inverse-Frobenius identity: the selected Gram inverse-trace equals
the sum of reciprocal leave-one-out residuals.

This is not a joint `poly(n,k)` inverse-norm bound and does not
close Milestone E. -/
theorem milestoneE_gram_inv_trace_eq_sum_inv_residual {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGram A J)⁻¹).trace =
      ∑ j ∈ J, (residualSq A (J.erase j) j)⁻¹ :=
  selectedColGram_inv_trace_eq_sum_inv_residual A J hG

/-- Elementary `σ_min` bound: `‖x‖² ≤ ‖A_J x‖² · tr(G_J⁻¹)`,
equivalently `σ_min(A_J) ≥ 1 / √tr(G⁻¹)`.

This is not a joint `poly(n,k)` inverse-norm bound and does not
close Milestone E. -/
theorem milestoneE_sigma_min_ge_inv_sqrt_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) (x : Fin J.card → ℝ) :
    vecEnergy x ≤
      vecEnergy (selectedCols A J *ᵥ x) *
        ((selectedColGram A J)⁻¹).trace :=
  selectedCols_energy_mul_inv_trace_ge A J hG x

/-- Implicit CPQR Gram–Schmidt factor is row-orthonormal: `R Rᵀ = I`.

This is not an inverse-norm bound and does not close Milestone E. -/
theorem milestoneE_gsR_mul_transpose {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    gsR A hA * (gsR A hA)ᵀ = 1 :=
  gsR_mul_transpose A hA

/-- Inverse-Frobenius proxy when the Gram–Schmidt factor `U` is
bidiagonal (`U_s t = 0` unless `t ∈ {s, s+1}`).

This is a hypothesis on the coefficient pattern of `U`, not a
static class of matrices `A`, and not Path 1. It is **not** a
joint `poly(n,k)` inverse-norm bound for every orthogonal-row
matrix. Multi-neighbor coupling remains open. It does not close
Milestone E. -/
theorem milestoneE_bidiagonal_U_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hbi : gsUBidiagonal A hA) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) :=
  pivotGram_inv_trace_le_of_bidiagonal A hA hbi

/-- CPQR inverse energy is at most `k · C(n,k)`.

This is exponential in `k` when `n ≈ 2k` and is **not** a joint
`poly(n,k)` inverse-norm bound. It does not close Milestone E. -/
theorem milestoneE_cpqr_inv_energy_le_choose {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n.choose k : ℝ) *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
  cpqr_inv_energy_le_choose A hA x

/-- Path 3: on the static class `min(k, n-k) ≤ d`, CPQR inverse
energy is at most `k · n^d`.

The extra hypothesis is the shape of `A` alone. It is **not** a
`poly(n,k)` theorem for every orthogonal-row matrix and does not
close Path 1. Milestone E remains open. -/
theorem milestoneE_cpqr_inv_energy_le_of_minDim {k n d : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hd : MinDimLe k n d) (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n : ℝ) ^ d *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
  cpqr_inv_energy_le_of_minDim A hA hd x
/-- Milestone E, `k = 2` only: the CPQR pivot-Gram inverse-trace is at
most `3(n-1)`.

This is the `k = 2` slice: Gram–Schmidt `U` is automatically bidiagonal
on `Fin 2`, so the nearest-neighbor inverse-trace bound applies to every
orthogonal-row `2 × n` matrix. It matches a joint polynomial bound for
two orthonormal rows. It does **not** close Milestone E (SPEC §16
outcome 1 needs all `k`). -/
theorem milestoneE_k2_inv_trace_le {n : ℕ}
    (A : Matrix (Fin 2) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ((pivotGram A hA)⁻¹).trace ≤ (3 : ℝ) * ((n : ℝ) - 1) :=
  pivotGram_inv_trace_le_of_k_eq_two A hA

/-- Additional column ℓ¹ budget bounds every inverse entry. Not a general CPQR claim. -/
theorem milestoneE_column_budget_S_abs_le_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hb : gsUColumnBudget A hA) (i j : Fin k) : |gsS A hA i j| ≤ 1 :=
  gsS_abs_le_one_of_column_budget A hA hb i j

/-- Polynomial inverse-trace under an extra coefficient budget; E remains open. -/
theorem milestoneE_column_budget_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hb : gsUColumnBudget A hA) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) :=
  pivotGram_inv_trace_le_of_column_budget A hA hb

/-- Actual volume-weighted inverse expectation; no full-support assumption. -/
theorem milestoneD_actual_expected_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * selectedInvTrace A J ≤
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  actual_expected_inv_trace_le A hA

/-- Expectation equality with the explicit additional nonsingular-support hypothesis. -/
theorem milestoneD_actual_expected_inv_trace_eq_of_full_support {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hfull : ∀ J : Finset (Fin n), J.card = k → (selectedColGram A J).det ≠ 0) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * selectedInvTrace A J =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  actual_expected_inv_trace_eq_of_full_support A hA hfull

/-- Singular square selections have zero probability mass. -/
theorem milestoneD_singular_volume_mass_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (fun J => (selectedColGram A J).det = 0), volumeWeight A J = 0 :=
  singular_volume_mass_zero A

/-- Finite volume probability of actual nonsingular inverse-trace control. -/
theorem milestoneD_actual_inv_trace_good_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInvTraceGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J :=
  actual_inv_trace_good_mass A hA hδ

/-- Actual inverse-energy RRQR probability bound, with literal vector quantification. -/
theorem milestoneD_actual_inverse_energy_good_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInverseEnergyGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J :=
  actual_inverse_energy_good_mass A hA hδ

/-- The original all-frame expectation equality fails, already for one row. -/
theorem milestoneD_actual_expectation_equality_obstruction :
    ∃ A : Matrix (Fin 1) (Fin 2) ℝ, OrthogonalRows A ∧
      (∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1,
        volumeWeight A J * selectedInvTrace A J) ≠ (2 : ℝ) := by
  refine ⟨ActualInverseWitness.zeroColumnFrame,
    ActualInverseWitness.zeroColumnFrame_orthogonal, ?_⟩
  rw [ActualInverseWitness.zeroColumnFrame_actual_expectation]
  norm_num

/-- Cauchy–Binet identifies retained k-volume with the retained row-Gram determinant. -/
theorem milestoneB_retained_volume_eq_det_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) :
    retainedVolume A S = (retainedGram A S).det :=
  retainedVolume_eq_det_gram A S

/-- The solve-based rejection score equals the exact deletion-volume ratio. -/
theorem milestoneB_reverse_score_eq_volume_ratio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) {i : Fin n}
    (hi : i ∈ S) (hV : retainedVolume A S ≠ 0) :
    reverseDeletionScore A S i = retainedVolume A (S.erase i) / retainedVolume A S :=
  reverse_score_eq_volume_ratio A S hi hV

/-- Exact rejection scores lie in the unit interval on a positive-volume parent. -/
theorem milestoneB_reverse_score_bounds {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) {i : Fin n}
    (hi : i ∈ S) (hV : 0 < retainedVolume A S) :
    0 ≤ reverseDeletionScore A S i ∧ reverseDeletionScore A S i ≤ 1 :=
  reverse_score_bounds A S hi hV

/-- Exact finite deletion normalization core, including zero-volume retained sets. -/
theorem milestoneB_reverse_deletion_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) :
    ∑ i ∈ S, retainedVolume A (S.erase i) =
      ((S.card - k : ℕ) : ℝ) * retainedVolume A S :=
  reverse_deletion_mass A S

/-- A positive-volume parent larger than k has a normalized deletion distribution. -/
theorem milestoneB_reverse_transition_normalization {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n))
    (hs : k < S.card) (hV : 0 < retainedVolume A S) :
    (∀ i ∈ S, 0 ≤ reverseDeleteProb A S i) ∧
      ∑ i ∈ S, reverseDeleteProb A S i = 1 :=
  ⟨fun i _ => reverseDeleteProb_nonneg A S i, reverse_transition_normalization A S hs hV⟩

/-- The literal reverse-deletion recursion ends in the volume-sampling law. -/
theorem milestoneD_reverse_sampler_law {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (J : Finset (Fin n)) :
    reverseEndpointMass A (n-k) univ J = volumeWeight A J :=
  reverse_sampler_law A hA J

/-- Actual inverse-energy RRQR guarantee for the finite reverse-sampling kernel. -/
theorem milestoneD_reverse_inverse_energy_good_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInverseEnergyGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      reverseEndpointMass A (n-k) univ J := by
  simpa only [reverse_sampler_law A hA] using (actual_inverse_energy_good_mass A hA hδ)

/-- Finite fast-stage proposal-mean sum bound; no machine runtime claim. -/
theorem milestoneD_reverse_fast_proposal_sum_le (k n : ℕ) :
    ∑ s ∈ Icc (2*k+1) n, (s : ℝ) / ((s-k : ℕ) : ℝ) ≤
      2 * ((n-2*k : ℕ) : ℝ) :=
  reverse_fast_proposal_sum_le k n

/-- A small-Frobenius block has an explicit finite Parseval completion. -/
theorem milestoneE_wide_completion_orthogonal {k : ℕ}
    (R : Matrix (Fin k) (Fin k) ℝ) (hR : frobEnergy R ≤ 1) (t : ℕ) (ht : 0 < t) :
    ∃ A : Matrix (Fin k) (Fin (k+k*t)) ℝ, OrthogonalRows A ∧
      (∀ i j : Fin k, A i (j.castAdd (k*t)) = R i j) ∧
      ∀ j : Fin (k*t), vecEnergy (fun i => A i (j.natAdd k)) ≤ (k : ℝ) / t :=
  wide_completion_orthogonal R hR t ht

/-- Triangular leading columns identify the projector without a pivot assumption. -/
theorem milestoneE_triangular_prefix_projector {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0) :
    ∀ t ≤ k, (selectedColGram A (widePrefix n t)).det ≠ 0 ∧
      ∀ x, selectedProjector A (widePrefix n t) *ᵥ x = prefixCut t x :=
  leading_prefix_projector hkn A hupper hdiag

/-- Exact coordinate-tail residual identity under finite triangular entry conditions. -/
theorem milestoneE_triangular_prefix_residual {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (t : ℕ) (ht : t ≤ k) (j : Fin n) :
    residualSq A (widePrefix n t) j = tailEnergy t (A.col j) :=
  residualSq_leading_tail hkn A hupper hdiag t ht j

/-- Strict tail-energy domination forces the actual greedy prefix sequence. -/
theorem milestoneE_triangular_prefix_pivots {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (htail : ∀ p : Fin k, ∀ j : Fin n, (p : ℕ) < (j : ℕ) →
      tailEnergy p (A.col j) < A p (Fin.castLE hkn p)^2) :
    ∀ t ≤ k, cpqrIterate A t = widePrefix n t :=
  triangular_prefix_pivots hkn A hupper hdiag htail

/-- Explicit candidate diagonal bound; no all-parameter adverse-family claim. -/
theorem milestoneE_wide_parameter_diagonal_lower {m : ℕ} (hm : 2 ≤ m)
    {i : ℕ} (hi : i < wideDim m) : wideAlpha m / 2 < wideDiagNat m i :=
  wideDiag_half_lower hm hi

/-- For every `m ≥ 2`, a Parseval frame, its actual CPQR prefix, and a
geometric inverse-energy witness. This is not a bound for every frame. -/
theorem milestoneE_wide_adverse_family {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      ∃ x : Fin (widePrefix (wideWidth m) (wideDim m)).card → ℝ,
        OrthogonalRows A ∧
        (∀ i j : Fin (wideDim m),
          A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        vecEnergy (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x) = 1 ∧
        wideGrowthLower m ^ 2 ≤ vecEnergy x :=
  wide_adverse_family hm

/-- Actual CPQR inverse energy beats every joint polynomial in `n` and `k`. -/
theorem milestoneE_cpqr_no_joint_polynomial (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x :=
  cpqr_no_joint_polynomial d hC

/-- The same family beats `max(n³, k³, (k(n-k+1))²)` in squared inverse energy. -/
theorem milestoneE_cpqr_named_polynomial_obstruction :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
          (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2))) ^ 2 *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x :=
  cpqr_named_polynomial_obstruction

/-- SPEC §11 in spectral norm, for a supplied orthonormal factor. -/
theorem milestoneF_cssp_spectral {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    spectralNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        spectralNorm E :=
  cssp_spectral A E U S Q hQ J hJ hInv hA

/-- SPEC §11 in Frobenius norm. The coefficient remains the spectral norm. -/
theorem milestoneF_cssp_frobenius {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    frobeniusNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        frobeniusNorm E :=
  cssp_frobenius A E U S Q hQ J hJ hInv hA

/-- The outcome-2 family leaves every fixed column-energy ratio.

This is not a polynomial bound for the leverage-ratio class, and it does
not close outcome 3. -/
theorem milestoneE_wide_leverage_escape {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ m : ℕ, 2 ≤ m ∧
      ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
        OrthogonalRows A ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        ∃ jMin jMax : Fin (wideWidth m),
          τ * residualSq A ∅ jMin < residualSq A ∅ jMax ∧
          (8 * (wideDim m : ℝ)) * residualSq A ∅ jMin < residualSq A ∅ jMax :=
  wide_leverage_escape hτ

/-- Appending a column adds `(1 + ‖G⁻¹ Bᵀ v‖²) / residual` to the inverse trace.

This is not a bound for the max-residual CPQR pivot and does not close
outcome 3. -/
theorem milestoneE_append_inv_trace_increment {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ)
    (hG : (Bᵀ * B).det ≠ 0)
    (hs : v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v))) ≠ 0) :
    (((appendColumn B v)ᵀ * appendColumn B v)⁻¹).trace =
      ((Bᵀ * B)⁻¹).trace +
        (1 + (((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) /
          (v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) :=
  append_inv_trace_increment B v hG hs

/-- Some unused column has positive residual and inverse-trace increment at
most `((n - t) + trace(G⁻¹) - t) / (k - t)`.

This is not a bound for the max-residual CPQR pivot and does not close
outcome 3. -/
theorem milestoneE_best_column_increment_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k) :
    ∃ j, j ∉ J ∧ 0 < residualSq A J j ∧
      (1 + (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) / residualSq A J j ≤
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) :=
  best_column_increment_le A hA J hG ht

/-- One appended column preserves the inductive inverse-trace bound.

This is not a bound for the max-residual CPQR pivot and does not close
outcome 3. -/
theorem milestoneE_inv_trace_growth_step {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1)) :
    ∃ j, j ∉ J ∧
      (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) :=
  inv_trace_growth_step A hA J hG ht hf

/-- Some `k` columns chosen by the increment bound have inverse trace at
most `k (n - k + 1)`.

This is not a bound for the max-residual CPQR pivot and does not close
outcome 3. -/
theorem milestoneE_minimizing_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ((selectedColGram A J)⁻¹).trace ≤ (k : ℝ) * ((n : ℝ) - k + 1) :=
  minimizing_inv_trace_le A hA

/-- Some `k` columns chosen by the increment bound satisfy
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

This is not a bound for the max-residual CPQR pivot and does not close
outcome 3. -/
theorem milestoneE_minimizing_inv_spectral_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ∀ x : Fin J.card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A J *ᵥ x) :=
  minimizing_inv_spectral_le A hA

/-- The least-index increment pivot selects `k` columns whose inverse
trace is at most `k (n - k + 1)` and which satisfy
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

This is not the max-residual CPQR pivot and does not close outcome 3. -/
theorem milestoneE_increment_set_bound {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (incrementSet A).card = k ∧
      (selectedColGram A (incrementSet A)).det ≠ 0 ∧
      ((selectedColGram A (incrementSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) ∧
      ∀ x : Fin (incrementSet A).card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A (incrementSet A) *ᵥ x) :=
  increment_set_bound A hA

/-- Max-residual CPQR and the least-index increment pivot select different
columns on an explicit orthogonal-row `2×5` frame.

This does not close outcome 1 or outcome 3. -/
theorem milestoneE_increment_set_ne_cpqr :
    ∃ A : Matrix (Fin 2) (Fin 5) ℝ,
      OrthogonalRows A ∧ incrementSet A ≠ cpqrSet A :=
  increment_set_ne_cpqr

/-- An orthogonal-row `2×5` frame with column energies in `[13/50, 16/25]`
has leverage ratio `32/13`, and on it max-residual CPQR and the increment
pivot select different columns.

Equal column energy still makes the second pivots agree. This witness does
not close outcome 1 or outcome 3. -/
theorem milestoneE_leverage_ratio_pivot_split :
    ∃ A : Matrix (Fin 2) (Fin 5) ℝ,
      OrthogonalRows A ∧
        (∀ j : Fin 5, (13 : ℝ) / 50 ≤ residualSq A ∅ j ∧
          residualSq A ∅ j ≤ (16 : ℝ) / 25) ∧
        residualSq A ∅ (0 : Fin 5) = (16 : ℝ) / 25 ∧
        residualSq A ∅ (2 : Fin 5) = (13 : ℝ) / 50 ∧
        ((16 : ℝ) / 25) / ((13 : ℝ) / 50) = 32 / 13 ∧
        incrementSet A ≠ cpqrSet A :=
  leverage_ratio_pivot_split

/-- Equal column energy and a pairwise-orthogonal selected block make the
next max-residual CPQR pivot agree with the increment pivot.

A one-column block is the agreement half of
`milestoneE_equal_energy_cpqr_prefix_trace`. The estimate
`‖G⁻¹ w‖² ≤ q / λ_min`, fed with the residual lower bound, sits above
the increment allowance except at this orthogonal endpoint, so it does
not finish the induction. This does not close outcome 3. -/
theorem milestoneE_equal_energy_orthogonal_block_same_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    cpqrPivot A J = incrementPivot A J :=
  equal_energy_orthogonal_block_same_pivot A hA hE hk hn J horth

/-- Equal column energy does not make every selected block agree.

On `blockFrame`, every column energy is `1/2` and columns `0` and `1`
have inner product `31/100`. After that block, max-residual CPQR takes
column `5` and the increment pivot takes column `3`. Column `5` is
orthogonal to column `0`. This block is not an orthogonal block, and the
statement does not say `cpqrSet ≠ incrementSet`. It does not close
outcome 3. -/
theorem milestoneE_equal_energy_block_pivot_split :
    OrthogonalRows blockFrame ∧
      (∀ i j : Fin 6, colInner blockFrame i i = colInner blockFrame j j) ∧
        colInner blockFrame 0 1 ≠ 0 ∧
          colInner blockFrame 0 5 = 0 ∧
            cpqrPivot blockFrame blockJ = some 5 ∧
              incrementPivot blockFrame blockJ = some 3 :=
  equal_energy_block_pivot_split

/-- Equal column energy does not make the third CPQR pivot agree with
the increment pivot.

On this orthogonal-row `3×6` frame every column energy is `1/2`. Both
rules take column `0` and then column `2`. After `{0, 2}`, max-residual
CPQR takes column `3` and the increment pivot takes column `5`, so the
three-column sets differ. Columns `0` and `2` are not orthogonal. This
does not close outcome 1 or outcome 3. -/
theorem milestoneE_equal_energy_third_pivot_split :
    OrthogonalRows pathFrame ∧
      (∀ i j : Fin 6, colInner pathFrame i i = colInner pathFrame j j) ∧
        colInner pathFrame 0 2 ≠ 0 ∧
          cpqrPivot pathFrame ∅ = some 0 ∧
            incrementPivot pathFrame ∅ = some 0 ∧
              cpqrPivot pathFrame ({0} : Finset (Fin 6)) = some 2 ∧
                incrementPivot pathFrame ({0} : Finset (Fin 6)) = some 2 ∧
                  cpqrPivot pathFrame pathJ = some 3 ∧
                    incrementPivot pathFrame pathJ = some 5 ∧
                      cpqrSet pathFrame ≠ incrementSet pathFrame :=
  equal_energy_third_pivot_split

/-- If every positive-residual unused column has coefficient zero, the
increment pivot and max-residual CPQR return the same column.

A nonzero coefficient can separate them, as in
`milestoneE_increment_set_ne_cpqr`. This does not close outcome 3. -/
theorem milestoneE_zero_coeff_same_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0)
    (hzero : ∀ j ∈ incrementCandidates A J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0) :
    incrementPivot A J = cpqrPivot A J :=
  zero_coeff_same_pivot A J hG hzero

/-- On pairwise orthogonal columns, max-residual CPQR selects `k` columns
with inverse trace at most `k (n - k + 1)` and
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

`ColumnIncoherent A 0` is read from `A`. It is stricter than the SPEC §10
target, and the adverse family is outside it. This does not close
outcome 3. -/
theorem milestoneE_incoherent_zero_cpqr_bound {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hC : ColumnIncoherent A 0) :
    (cpqrSet A).card = k ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
  incoherent_zero_cpqr_bound A hA hC

/-- For every `m ≥ 2`, the outcome-2 frame is orthogonal across rows and
is not pairwise orthogonal across columns.

Phase P's CPQR bound does not apply to that frame. This does not close
outcome 3. -/
theorem milestoneE_wide_not_incoherent_zero {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      OrthogonalRows A ∧ ¬ ColumnIncoherent A 0 :=
  wide_not_incoherent_zero hm

/-- For every `ρ > 0`, absolute inner-product incoherence does not restore
a polynomial CPQR bound.

Some orthogonal-row frame in `ColumnIncoherent A ρ` has a CPQR block whose
inverse energy exceeds `C (n + k + 1)^{2d}`. The predicate bounds absolute
inner products, not the normalized coherence ratio in SPEC §10. The case
`ρ = 0` is unchanged. This does not close outcome 1 or outcome 3. -/
theorem milestoneE_incoherent_no_joint_polynomial {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ)
    {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        ColumnIncoherent A ρ ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x :=
  incoherent_no_joint_polynomial hρ d hC

/-- The outcome-2 frame repeats a positive completion column, so two
distinct columns are equal and their normalized coherence is `1`.

That same frame beats every polynomial `C (n + k + 1)^{2d}`. A class
that requires every normalized ratio to be at most some `ρ < 1`
excludes the frame. This does not prove a polynomial CPQR bound on the
matrices that meet a stricter ratio. Absolute inner-product incoherence
is a different predicate. This does not close outcome 1 or outcome 3. -/
theorem milestoneE_normalized_coherence_one (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (∃ j1 j2 : Fin n, j1 ≠ j2 ∧ (∀ i, A i j1 = A i j2) ∧
          0 < residualSq A ∅ j1 ∧
          |colInner A j1 j2| /
            (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2)) = 1) ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x :=
  normalized_coherence_one d hC

/-- The design-padded adverse family. For every `m ≥ 2`, every completion
`C` of the triangular block, and every tight design `W` with `W Wᵀ = 1`
and column energy at most `1 / wideRepeats m`, the frame `[R | C W]` has
orthogonal rows, CPQR takes the leading prefix, the image energy is `1`,
and the inverse energy is at least `wideGrowthLower m ^ 2`.

The repeated frame is the design `(1/√t)[I ⋯ I]`. No coherence bound on
the resulting columns is claimed. This does not close outcome 1 or
outcome 3. -/
theorem milestoneE_design_adverse_family {m : ℕ} (hm : 2 ≤ m) {N : ℕ}
    (C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ)
    (hCC : wideTriangular m * (wideTriangular m)ᵀ + C * Cᵀ = 1)
    (W : Matrix (Fin (wideDim m)) (Fin N) ℝ) (hW : W * Wᵀ = 1)
    (hcol : ∀ j : Fin N, vecEnergy (fun q => W q j) ≤ 1 / (wideRepeats m : ℝ)) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + N)) ℝ,
      ∃ x : Fin (widePrefix (wideDim m + N) (wideDim m)).card → ℝ,
        OrthogonalRows A ∧
        (∀ i j : Fin (wideDim m), A i (j.castAdd N) = wideTriangular m i j) ∧
        (∀ (i : Fin (wideDim m)) (j : Fin N),
          A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
        cpqrSet A = widePrefix (wideDim m + N) (wideDim m) ∧
        vecEnergy (selectedCols A (widePrefix (wideDim m + N) (wideDim m)) *ᵥ x) = 1 ∧
        wideGrowthLower m ^ 2 ≤ vecEnergy x :=
  wide_design_adverse_family hm C hCC W hW hcol

/-- A symmetric completion of any `R` with `‖R‖_F² ≤ 1`:
`Cᵀ = C`, `R Rᵀ + C Cᵀ = 1`, `⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`,
`(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and `‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`.

This is the completion a later phase feeds into the design frame. No
coherence bound on any frame is claimed. This does not close outcome 1
or outcome 3. -/
theorem milestoneE_symmetric_completion {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) :
    ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Cᵀ = C ∧ R * Rᵀ + C * Cᵀ = 1 ∧
      (∀ w v : Fin k → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - (Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v)) ∧
      (∀ w : Fin k → ℝ,
        (1 - frobEnergy R) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      ∀ v : Fin k → ℝ, vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy R ^ 2 * vecEnergy v :=
  symmetric_completion R hR

/-- The weighted signed triple design: for every `n`, a tight design
`W Wᵀ = 1` in `ℝ^(n+3)` with `4 (n+3)(n+2)(n+1)` columns, every column of
energy `1 / (4 (n+2)(n+1))`, and every pair of distinct columns at
normalized inner product at most `13/14`.

This is the explicit design a later phase feeds into the design frame.
Its column energy is above the `1 / wideRepeats` cap of
`milestoneE_design_adverse_family`, so no adverse frame is built here.
No coherence bound on any orthogonal-row frame is claimed. This does
not close outcome 1 or outcome 3. -/
theorem milestoneE_triple_design (n : ℕ) :
    ∃ W : Matrix (Fin (n + 3)) (Fin (4 * ((n + 3) * (n + 2) * (n + 1)))) ℝ,
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) = 1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1)))) ∧
      ∀ a b, a ≠ b →
        |∑ i, W i a * W i b| ≤
          13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
            Real.sqrt (vecEnergy (fun i => W i b))) :=
  triple_design n

/-- The scaled triple-design frame: for every `m ≥ 3`, the frame
`A = [3 R₀ | C W]` with `R₀ = wideTriangular m`, the symmetric completion
`C` of `3 R₀`, and the reindexed triple design `W` has `A Aᵀ = 1`, CPQR
set equal to the leading prefix, image energy `1`, and inverse energy at
least `wideGrowthLower m ^ 2 / 9`. The statement records the completion
identities of `C` (`Cᵀ = C`, the inner-product identity, the energy
sandwich, the perturbation bound, and `‖3 R₀‖_F² ≤ 45 / (16 k)`) and the
design properties of `W` (`W Wᵀ = 1`, column energy
`1 / (4 (k-1)(k-2))`, pairwise normalized inner product at most `13/14`).

No coherence bound on the columns of `A` is claimed: the `13/14` bound is
about `W`, not about `C W` or about the leading columns. This does not
close outcome 1 or outcome 3. -/
theorem milestoneE_scaled_triple_frame {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + tripleCount (wideDim m - 3))) ℝ,
    ∃ C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ,
    ∃ W : Matrix (Fin (wideDim m)) (Fin (tripleCount (wideDim m - 3))) ℝ,
    ∃ x : Fin (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)).card → ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin (wideDim m), A i (j.castAdd _) = scaledBlock m i j) ∧
      (∀ (i : Fin (wideDim m)) (j : Fin (tripleCount (wideDim m - 3))),
        A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
      Cᵀ = C ∧ scaledBlock m * (scaledBlock m)ᵀ + C * Cᵀ = 1 ∧
      frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) ∧
      (∀ w v : Fin (wideDim m) → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - ((scaledBlock m)ᵀ *ᵥ w) ⬝ᵥ ((scaledBlock m)ᵀ *ᵥ v)) ∧
      (∀ w : Fin (wideDim m) → ℝ,
        (1 - frobEnergy (scaledBlock m)) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      (∀ v : Fin (wideDim m) → ℝ,
        vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy (scaledBlock m) ^ 2 * vecEnergy v) ∧
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) =
        1 / (4 * (((wideDim m : ℝ) - 1) * ((wideDim m : ℝ) - 2)))) ∧
      (∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
        13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
          Real.sqrt (vecEnergy (fun i => W i b)))) ∧
      cpqrSet A = widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m) ∧
      vecEnergy (selectedCols A
        (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)) *ᵥ x) = 1 ∧
      wideGrowthLower m ^ 2 / 9 ≤ vecEnergy x :=
  scaled_triple_frame hm

/-- Filler–filler and leading–filler normalized coherence of the scaled
triple-design frame. For every `m ≥ 3` and `ε = 45 / (16 k)`, distinct filler
columns have normalized coherence at most `(13/14 + ε)/(1 - ε)`, and each
leading column against each filler has normalized coherence at most
`(3(1 + 1/m)/√14 + ε)/√(1 - ε)`.

No leading–leading bound is proved. No coherence bound on the whole frame is
claimed. This is not a polynomial CPQR bound, and outcome 3 stays open. -/
theorem milestoneE_scaled_triple_frame_filler_coherence {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + tripleCount (wideDim m - 3))) ℝ,
    ∃ C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ,
    ∃ W : Matrix (Fin (wideDim m)) (Fin (tripleCount (wideDim m - 3))) ℝ,
    ∃ x : Fin (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)).card → ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin (wideDim m), A i (j.castAdd _) = scaledBlock m i j) ∧
      (∀ (i : Fin (wideDim m)) (j : Fin (tripleCount (wideDim m - 3))),
        A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
      Cᵀ = C ∧ scaledBlock m * (scaledBlock m)ᵀ + C * Cᵀ = 1 ∧
      frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) ∧
      (∀ w v : Fin (wideDim m) → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - ((scaledBlock m)ᵀ *ᵥ w) ⬝ᵥ ((scaledBlock m)ᵀ *ᵥ v)) ∧
      (∀ w : Fin (wideDim m) → ℝ,
        (1 - frobEnergy (scaledBlock m)) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      (∀ v : Fin (wideDim m) → ℝ,
        vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy (scaledBlock m) ^ 2 * vecEnergy v) ∧
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) =
        1 / (4 * (((wideDim m : ℝ) - 1) * ((wideDim m : ℝ) - 2)))) ∧
      (∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
        13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
          Real.sqrt (vecEnergy (fun i => W i b)))) ∧
      cpqrSet A = widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m) ∧
      vecEnergy (selectedCols A
        (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)) *ᵥ x) = 1 ∧
      wideGrowthLower m ^ 2 / 9 ≤ vecEnergy x ∧
      (∀ a b : Fin (tripleCount (wideDim m - 3)), a ≠ b →
        |∑ i, A i (a.natAdd (wideDim m)) * A i (b.natAdd (wideDim m))| ≤
          (13 / 14 + 45 / (16 * (wideDim m : ℝ))) / (1 - 45 / (16 * (wideDim m : ℝ))) *
            (Real.sqrt (vecEnergy (fun i => A i (a.natAdd (wideDim m)))) *
              Real.sqrt (vecEnergy (fun i => A i (b.natAdd (wideDim m)))))) ∧
      ∀ (j : Fin (wideDim m)) (a : Fin (tripleCount (wideDim m - 3))),
        |∑ i, A i (j.castAdd _) * A i (a.natAdd (wideDim m))| ≤
          (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + 45 / (16 * (wideDim m : ℝ))) /
              Real.sqrt (1 - 45 / (16 * (wideDim m : ℝ))) *
            (Real.sqrt (vecEnergy (fun i => A i (j.castAdd _))) *
              Real.sqrt (vecEnergy (fun i => A i (a.natAdd (wideDim m))))) :=
  scaled_triple_frame_filler_coherence hm

/-- Leading–leading normalized coherence of `scaledBlock m = (3 : ℝ) • wideTriangular m`.
For every `m ≥ 2` and all `i ≠ j`, the absolute inner product of those columns
is at most `(1/2 + 1/m)` times the product of their Euclidean norms.

This does not bound filler pairs. This does not bound the whole frame: a
leading–leading ratio `≤ 1/2 + 1/m` is not a coherence bound on the whole
frame. This does not close outcome 3. This is not a polynomial CPQR bound. -/
theorem milestoneE_scaled_block_leading_coherence {m : ℕ} (hm : 2 ≤ m)
    {i j : Fin (wideDim m)} (hij : i ≠ j) :
    |∑ row, scaledBlock m row i * scaledBlock m row j| ≤
      (1 / 2 + 1 / (m : ℝ)) *
        (Real.sqrt (vecEnergy (fun row => scaledBlock m row i)) *
          Real.sqrt (vecEnergy (fun row => scaledBlock m row j))) :=
  leading_leading_ratio hm hij

/-- Normalized coherence at most `19/20` does not restore a polynomial CPQR
bound. For every degree and every positive coefficient, some orthogonal-row
frame has positive column energy, normalized coherence at most `19/20`, and
CPQR inverse energy strictly above `C (n + k + 1)^{2d}`. Any cap `ρ ≥ 19/20`
is too weak for the same reason, since coherence at most `19/20` implies
coherence at most `ρ`. This does not close outcome 3. It is not a polynomial
bound for every orthogonal-row matrix. A stricter coherence cap is not ruled
out. -/
theorem milestoneE_bounded_coherence_no_polynomial (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (∀ j, 0 < residualSq A ∅ j) ∧
        (∀ j1 j2, j1 ≠ j2 →
          |colInner A j1 j2| ≤ (19 / 20) *
            (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2))) ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x :=
  bounded_coherence_no_polynomial d hC

/-- Equal column energy makes the second CPQR pivot agree with the
increment pivot, and the two-column inverse trace is at most
`2 (n - 1) / (k - 1)`.

This is leverage ratio `1`. It does not bound later pivots and does
not close outcome 3. -/
theorem milestoneE_equal_energy_cpqr_prefix_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 2 ≤ k) (hn : 0 < n) :
    cpqrPivot A ∅ = some ⟨0, hn⟩ ∧
    cpqrPivot A {⟨0, hn⟩} = incrementPivot A {⟨0, hn⟩} ∧
    (selectedColGram A (cpqrIterate A 2)).det ≠ 0 ∧
    ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
      (2 : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) :=
  equal_energy_cpqr_prefix_trace A hA hE hk hn

/-- Equal column energy makes the two-column CPQR Rayleigh quotient at
least `(k - 1) / (2 (n - 1))`.

This bounds only that prefix. It does not bound a `k`-set for `k > 2`
and does not close outcome 3. -/
theorem milestoneE_equal_energy_cpqr_prefix_rayleigh {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 2 ≤ k) (hn : 0 < n)
    (x : Fin (cpqrIterate A 2).card → ℝ) :
    ((k : ℝ) - 1) / (2 * ((n : ℝ) - 1)) * vecEnergy x ≤
      vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x) :=
  equal_energy_cpqr_prefix_rayleigh A hA hE hk hn x

/-- Equal column energy makes the CPQR three-column inverse trace at most
the two-column bound plus one Rayleigh-controlled step.

This bounds only that prefix. It does not bound a `k`-set for `k > 3`
and does not close outcome 3. -/
theorem milestoneE_equal_energy_cpqr_three_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 3 ≤ k) (hn : 0 < n) :
    (selectedColGram A (cpqrIterate A 3)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A 3))⁻¹).trace ≤
        (2 : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) +
          (1 + (2 * (k : ℝ) * ((n : ℝ) - 1)) / ((n : ℝ) * ((k : ℝ) - 1))) *
            (((n : ℝ) - 2) / ((k : ℝ) - 2)) :=
  equal_energy_cpqr_three_trace A hA hE hk hn

/-- For three rows, equal column energy makes the full CPQR set obey
`5n - 12 + 6/n` in inverse trace and in inverse energy.

This is the phase-T prefix identified with `cpqrSet` at `k = 3`. It is
not a bound for general `k` and does not close outcome 3. -/
theorem milestoneE_equal_energy_cpqr_k3 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : k = 3) (hn : 0 < n) :
    (cpqrSet A).card = 3 ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (5 : ℝ) * (n : ℝ) - 12 + 6 / (n : ℝ) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
            ((5 : ℝ) * (n : ℝ) - 12 + 6 / (n : ℝ)) :=
  equal_energy_cpqr_k3 A hA hE hk hn

/-- Every 2-column Gram is invertible, and its inverse trace is at most
`2 τ^2 n / (k (1 - ρ^2))`, when orthogonal rows have leverage ratio at
most `τ` and normalized coherence at most `ρ < 1`.

This bounds every 2-column Gram under a leverage-ratio and coherence
hypothesis. It does not bound a `k`-set for `k > 2`. It does not close
outcome 3. It is not a polynomial CPQR bound for every orthogonal-row
matrix. The census did not prove this. It does not identify
`cpqrIterate A 2`. -/
theorem milestoneE_joint_pair_inv_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 1 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    ∀ i j : Fin n, i ≠ j →
      (selectedColGram A {i, j}).det ≠ 0 ∧
        ((selectedColGram A {i, j})⁻¹).trace ≤
          (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) :=
  joint_pair_inv_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh

/-- The CPQR prefix of length 2 under the joint leverage-ratio and
coherence hypothesis. It does not bound later pivots. It does not close
outcome 3. It is not a polynomial bound for every orthogonal-row matrix. -/
theorem milestoneE_joint_cpqr_prefix_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    ∃ j0 j1 : Fin n, j0 ≠ j1 ∧
      cpqrIterate A 2 = {j0, j1} ∧
      (selectedColGram A (cpqrIterate A 2)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) :=
  joint_cpqr_prefix_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh

/-- Rayleigh form of the length-2 CPQR prefix under the joint leverage-ratio
and coherence hypothesis. Not sharp. Does not bound later pivots. Does not
close outcome 3. Not a polynomial bound for every orthogonal-row matrix. -/
theorem milestoneE_joint_cpqr_prefix_rayleigh {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (x : Fin (cpqrIterate A 2).card → ℝ) :
    ((k : ℝ) * (1 - ρ ^ 2)) / ((2 : ℝ) * τ ^ 2 * (n : ℝ)) * vecEnergy x ≤
      vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x) :=
  joint_cpqr_prefix_rayleigh A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh x

/-- Third CPQR pivot under the joint leverage-ratio and coherence
hypothesis. Does not bound pivots after the third. Does not close
outcome 3. Not a polynomial bound for every orthogonal-row matrix.
Not claimed sharp. -/
theorem milestoneE_joint_cpqr_three_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 3 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (selectedColGram A (cpqrIterate A 3)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A 3))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) +
          (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) *
            (((n : ℝ) - 2) / ((k : ℝ) - 2)) :=
  joint_cpqr_three_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh

/-- For three rows, the joint leverage-ratio and coherence hypothesis bounds
the full CPQR set, not only a prefix.

This is the phase-AM prefix identified with `cpqrSet` at `k = 3`. It is
not a bound for general `k`. It does not close outcome 3. It is not sharp. -/
theorem milestoneE_joint_cpqr_k3 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : k = 3) (hn : 0 < n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (cpqrSet A).card = 3 ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
          (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
            ((2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
              (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2)) :=
  joint_cpqr_k3 A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh

/-- One CPQR pivot step under a leverage-ratio bound, assuming a trace
bound on the current prefix. Not a bound on the full `k`-set. Not a
polynomial bound. Does not close outcome 3. Coherence is not used. -/
theorem milestoneE_joint_cpqr_step {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (ht1 : 1 ≤ t) (htk : t < k) (htn : t < n) (τ B : ℝ)
    (hτ : 1 ≤ τ) (hB : 0 ≤ B)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (htr : ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B) :
    (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
        B + (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
          (((n : ℝ) - t) / ((k : ℝ) - t)) :=
  joint_cpqr_step A hA ht1 htk htn τ B hτ hB hlev htr

/-- Tighter than `milestoneE_joint_cpqr_step` by one copy of the current
trace. Still one step. Not an iteration. Not a polynomial bound. Does
not close outcome 3. -/
theorem milestoneE_joint_cpqr_step_tight {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (ht1 : 1 ≤ t) (htk : t < k) (htn : t < n) (τ B : ℝ)
    (hτ : 1 ≤ τ) (hB : 0 ≤ B)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (htr : ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B) :
    (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
        (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
          (((n : ℝ) - t) / ((k : ℝ) - t)) :=
  joint_cpqr_step_tight A hA ht1 htk htn τ B hτ hB hlev htr

/-- For every prefix length `2 ≤ t ≤ k`, the CPQR Gram inverse trace is at
most `jointTraceBound`. The same bound controls the Rayleigh comparison.
This is not a polynomial in `k`. It does not close outcome 3. It is not a
bound for matrices outside the leverage-ratio and coherence hypotheses. -/
theorem milestoneE_joint_cpqr_trace_bound {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (ht2 : 2 ≤ t) (htk : t ≤ k) :
    (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
        jointTraceBound k n τ ρ t ∧
      ∀ x : Fin (cpqrIterate A t).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) *
            jointTraceBound k n τ ρ t :=
  joint_cpqr_trace_bound A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh ht2 htk

/-- Square equal-leverage only. Not a polynomial bound for rectangular or
`τ > 1` matrices. Does not close outcome 3. Not claimed sharp for `ρ > 0`.
On the identity at `ρ = 0` the bound equals `k`, and the inverse trace
equals `k`. -/
theorem milestoneE_joint_square_equal_trace {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin k, residualSq A ∅ i ≤ residualSq A ∅ j)
    (hcoh : ∀ i j : Fin k, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (cpqrSet A).card = k ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) - 2 + 2 / (1 - ρ ^ 2) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
            ((k : ℝ) - 2 + 2 / (1 - ρ ^ 2)) :=
  joint_square_equal_trace A hA hk ρ hρ0 hρ hlev hcoh

end StructuredColumnSelection
