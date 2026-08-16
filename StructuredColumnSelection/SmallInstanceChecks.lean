import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.CPQRVolume
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum

/-!
# Small exact volume-weight checks

Rational orthogonal-row frames used as independent witnesses of
Milestones B–E. The sums and CPQR runs below are evaluated by
enumerating subsets or executing the greedy residual rule; they do
not invoke the general Cauchy–Binet or inverse-Gram theorems.
-/

namespace StructuredColumnSelection
namespace SmallInstance

open Matrix Finset

/-- A `2×3` orthogonal-row frame with rational entries. -/
def frame23 : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 0, 0; 0, (3 : ℚ) / 5, (4 : ℚ) / 5]

theorem frame23_mul_transpose :
    frame23 * frame23ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

private lemma powersetCard_fin3 :
    (univ : Finset (Fin 3)).powersetCard 2 =
      {({0, 1} : Finset (Fin 3)), {0, 2}, {1, 2}} := by
  native_decide

private lemma volumeWeight_frame23_01 :
    volumeWeight frame23 ({0, 1} : Finset (Fin 3)) = (9 : ℚ) / 25 := by
  native_decide

private lemma volumeWeight_frame23_02 :
    volumeWeight frame23 ({0, 2} : Finset (Fin 3)) = (16 : ℚ) / 25 := by
  native_decide

private lemma volumeWeight_frame23_12 :
    volumeWeight frame23 ({1, 2} : Finset (Fin 3)) = 0 := by
  native_decide

/-- Direct enumeration: `(3/5)² + (4/5)² + 0 = 1`. -/
theorem frame23_volume_sum :
    ∑ J ∈ (univ : Finset (Fin 3)).powersetCard 2, volumeWeight frame23 J = 1 := by
  rw [powersetCard_fin3, sum_insert, sum_insert, sum_singleton,
    volumeWeight_frame23_01, volumeWeight_frame23_02, volumeWeight_frame23_12]
  · norm_num
  · native_decide
  · native_decide

/-- A `1×2` Parseval frame. -/
def frame12 : Matrix (Fin 1) (Fin 2) ℚ :=
  !![(3 : ℚ) / 5, (4 : ℚ) / 5]

theorem frame12_mul_transpose :
    frame12 * frame12ᵀ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  native_decide

private lemma powersetCard_fin2 :
    (univ : Finset (Fin 2)).powersetCard 1 =
      {({0} : Finset (Fin 2)), {1}} := by
  native_decide

private lemma volumeWeight_frame12_0 :
    volumeWeight frame12 ({0} : Finset (Fin 2)) = (9 : ℚ) / 25 := by
  native_decide

private lemma volumeWeight_frame12_1 :
    volumeWeight frame12 ({1} : Finset (Fin 2)) = (16 : ℚ) / 25 := by
  native_decide

theorem frame12_volume_sum :
    ∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1, volumeWeight frame12 J = 1 := by
  rw [powersetCard_fin2, sum_insert, sum_singleton,
    volumeWeight_frame12_0, volumeWeight_frame12_1]
  · norm_num
  · native_decide

private lemma invGram_frame23_01 :
    volumeWeightedInvGram frame23 ({0, 1} : Finset (Fin 3)) =
      !![((9 : ℚ) / 25), 0; 0, 1] := by
  native_decide

private lemma invGram_frame23_02 :
    volumeWeightedInvGram frame23 ({0, 2} : Finset (Fin 3)) =
      !![((16 : ℚ) / 25), 0; 0, 1] := by
  native_decide

private lemma invGram_frame23_12 :
    volumeWeightedInvGram frame23 ({1, 2} : Finset (Fin 3)) =
      !![1, 0; 0, 0] := by
  native_decide

/-- Direct enumeration: the three adjugates sum to `2 • I`. -/
theorem frame23_inverse_gram_sum :
    ∑ J ∈ (univ : Finset (Fin 3)).powersetCard 2, volumeWeightedInvGram frame23 J =
      (2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
  rw [powersetCard_fin3, sum_insert, sum_insert, sum_singleton,
    invGram_frame23_01, invGram_frame23_02, invGram_frame23_12]
  · ext i j
    fin_cases i <;> fin_cases j <;> native_decide
  · native_decide
  · native_decide

private lemma invGram_frame12_0 :
    volumeWeightedInvGram frame12 ({0} : Finset (Fin 2)) = 1 := by
  native_decide

private lemma invGram_frame12_1 :
    volumeWeightedInvGram frame12 ({1} : Finset (Fin 2)) = 1 := by
  native_decide

theorem frame12_inverse_gram_sum :
    ∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1, volumeWeightedInvGram frame12 J =
      (2 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
  rw [powersetCard_fin2, sum_insert, sum_singleton,
    invGram_frame12_0, invGram_frame12_1]
  · ext i j
    fin_cases i
    fin_cases j
    native_decide
  · native_decide

/-- Direct traces: `34/25 + 41/25 + 1 = 4 = 2 · (3 - 2 + 1)`. -/
theorem frame23_expected_inv_frob :
    ∑ J ∈ (univ : Finset (Fin 3)).powersetCard 2, invFrobWeight frame23 J = 4 := by
  simp [invFrobWeight, ← Matrix.trace_sum, frame23_inverse_gram_sum,
    Matrix.trace_smul, Matrix.trace_one]
  norm_num

theorem frame12_expected_inv_frob :
    ∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1, invFrobWeight frame12 J = 2 := by
  simp [invFrobWeight, ← Matrix.trace_sum, frame12_inverse_gram_sum,
    Matrix.trace_smul, Matrix.trace_one]

/-- CPQR on `frame23` selects columns `{0,2}` (largest leverage, then
largest residual). -/
theorem frame23_cpqr_set :
    cpqrSet frame23 = ({0, 2} : Finset (Fin 3)) := by
  native_decide

/-- CPQR on `frame12` selects the larger column. -/
theorem frame12_cpqr_set :
    cpqrSet frame12 = ({1} : Finset (Fin 2)) := by
  native_decide

/-- Direct leverage sum: `1 + 9/25 + 16/25 = 2`. -/
theorem frame23_leverage_sum :
    ∑ j : Fin 3, residualSq frame23 ∅ j = 2 := by
  native_decide

/-- First pivot is the unique maximal-leverage column. -/
theorem frame23_first_pivot :
    cpqrPivot frame23 ∅ = some 0 := by
  native_decide

theorem frame23_cpqr_card :
    (cpqrSet frame23).card = 2 := by
  rw [frame23_cpqr_set]
  native_decide

theorem frame12_cpqr_card :
    (cpqrSet frame12).card = 1 := by
  rw [frame12_cpqr_set]
  native_decide

/-- Direct volume: CPQR on `frame12` selects `(4/5)² = 16/25 ≥ 1/2`. -/
theorem frame12_k1_volume :
    volumeWeight frame12 (cpqrSet frame12) = (16 : ℚ) / 25 := by
  rw [frame12_cpqr_set, volumeWeight_frame12_1]

/-- After `{0}`, residuals are `0 + 9/25 + 16/25 = 1 = 2 - 1`. -/
theorem frame23_residual_energy_after_0 :
    ∑ j : Fin 3, residualSq frame23 ({0} : Finset (Fin 3)) j = 1 := by
  native_decide

/-- After `{0}`, the unused max residual is `16/25 ≥ 1/2`. -/
theorem frame23_next_residual_after_0 :
    (1 : ℚ) / 2 ≤ residualSq frame23 ({0} : Finset (Fin 3)) 2 := by
  native_decide

/-- Direct binomial comparison: `16/25 ≥ 1 / C(3,2) = 1/3`. -/
theorem frame23_binomial_volume :
    (1 : ℚ) / 3 ≤ volumeWeight frame23 (cpqrSet frame23) := by
  rw [frame23_cpqr_set, volumeWeight_frame23_02]
  native_decide

/-- Direct binomial comparison: `16/25 ≥ 1 / C(2,1) = 1/2`. -/
theorem frame12_binomial_volume :
    (1 : ℚ) / 2 ≤ volumeWeight frame12 (cpqrSet frame12) := by
  rw [frame12_k1_volume]
  native_decide

/-! ### Certified `r_CPQR > 1` witness (C = 1 counterexample)

`frame38` is a rational `3×8` orthogonal-row matrix on which ordinary
CPQR selects columns `{0, 1, 2}` while the selected block has a
singular value below `1/√18`, i.e. `‖A_J⁻¹‖₂ > √(k(n-k+1))`. This
refutes the ideal `C = 1` workshop-scale bound. The witness is far
below every named polynomial (`max(n³, k³, (k(n-k+1))²) = 512`), so
Milestone E stays OPEN (SPEC §16 outcome 2 is a *machine-checked
counterexample*; this certificate is the `C = 1` special case).

Provenance: SLSQP adverse search in the row-trapezoidal
parametrization (strict pivot-margin floor `2×10⁻³`), then a rational
Cayley-transform re-parametrization (coefficient denominator `10⁴`),
then exact certification in ℚ: `AAᵀ = I`, every pivot margin strictly
positive (minimum `≈ 1.78×10⁻³`), and the inverse-norm lower bound
via the explicit rational test vector below. Full record:
`experiments/cpqr_r_gt_1_witness_3_8.json`.
-/

/-- The certified `3×8` rational orthogonal-row CPQR witness. -/
def frame38 : Matrix (Fin 3) (Fin 8) ℚ :=
  !![
    ((3875327271587471739122796338825603 : ℚ) / 5433644339183757333293380411174397), ((33080315996430581254342847665480000 : ℚ) / 70637376409388845332813945345267161), (-(33234586449631383673439144534530000 : ℚ) / 70637376409388845332813945345267161), (-(8647746605122426503895656066660000 : ℚ) / 70637376409388845332813945345267161), ((3750448977575622889592262703400000 : ℚ) / 70637376409388845332813945345267161), ((8654911025192579199555355207220000 : ℚ) / 70637376409388845332813945345267161), (-(8655539699923975855605376687390000 : ℚ) / 70637376409388845332813945345267161), ((3748249565660503172469290912090000 : ℚ) / 70637376409388845332813945345267161);
    ((306686546004074227834368040000 : ℚ) / 5433644339183757333293380411174397), ((37877113065131977716358845192232839 : ℚ) / 70637376409388845332813945345267161), ((24179290770860588362228755666805000 : ℚ) / 70637376409388845332813945345267161), ((24322902389788522530507181489030000 : ℚ) / 70637376409388845332813945345267161), ((24382597565826882225810024011510000 : ℚ) / 70637376409388845332813945345267161), (-(24386148760286194482032236158260000 : ℚ) / 70637376409388845332813945345267161), ((24385234164233267258229149131805000 : ℚ) / 70637376409388845332813945345267161), ((24390297096426521012057147561945000 : ℚ) / 70637376409388845332813945345267161);
    ((675184486701012177592898810000 : ℚ) / 5433644339183757333293380411174397), ((4356029305662815783447858195000 : ℚ) / 70637376409388845332813945345267161), (-(28983327604234595073632867757767161 : ℚ) / 70637376409388845332813945345267161), ((28807791813129660304569526588530000 : ℚ) / 70637376409388845332813945345267161), (-(28805826211100419458476564268885000 : ℚ) / 70637376409388845332813945345267161), (-(28808338688255858833537260993510000 : ℚ) / 70637376409388845332813945345267161), ((28808351570366738716672871038255000 : ℚ) / 70637376409388845332813945345267161), (-(28811448764991543201062985153900000 : ℚ) / 70637376409388845332813945345267161)]

/-- Orthonormality of the witness, exactly. -/
theorem frame38_mul_transpose :
    frame38 * frame38ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

/-- CPQR on `frame38` selects columns `{0, 1, 2}` (every pivot margin
is strictly positive, so the smallest-index tie break is never used). -/
theorem frame38_cpqr_set :
    cpqrSet frame38 = ({0, 1, 2} : Finset (Fin 8)) := by
  native_decide

/-- Test vector for the inverse-norm lower bound on the selected block. -/
private def frame38TestVec : Fin 3 → ℚ :=
  ![(-(180013 : ℚ) / 250000), ((122339 : ℚ) / 250000), (-(491991 : ℚ) / 1000000)]

/-- Inverse-norm lower bound certificate: `18 ‖A_J x‖² < ‖x‖²` implies
`σ_min(A_J)² < 1/18`, hence `‖A_J⁻¹‖₂ > √18 = √(k(n-k+1))` and
`r_CPQR > 1`. This is a `C = 1` counterexample certificate, not a
polynomial-bound refutation: `4.38 ≪ 512 = max(n³, k³, (k(n-k+1))²)`.
Milestone E remains OPEN. -/
theorem frame38_inv_norm_lb :
    (18 : ℚ) * (∑ i : Fin 3,
        (frame38 i 0 * frame38TestVec 0 +
         frame38 i 1 * frame38TestVec 1 +
         frame38 i 2 * frame38TestVec 2) ^ 2) <
      ∑ i : Fin 3, frame38TestVec i ^ 2 := by
  native_decide

end SmallInstance
end StructuredColumnSelection
