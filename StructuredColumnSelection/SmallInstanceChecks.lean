import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
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

end SmallInstance
end StructuredColumnSelection
