import StructuredColumnSelection.VolumeWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Small exact volume-weight checks

Rational orthogonal-row frames used as independent witnesses of
Milestone B. The sums below are evaluated by enumerating subsets; they
do not invoke the general Cauchy–Binet theorem.
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
  rw [powersetCard_fin3]
  simp [volumeWeight_frame23_01, volumeWeight_frame23_02, volumeWeight_frame23_12]
  norm_num

/-- A `1×2` Parseval frame. -/
def frame12 : Matrix (Fin 1) (Fin 2) ℚ :=
  !![(3 : ℚ) / 5, (4 : ℚ) / 5]

theorem frame12_mul_transpose :
    frame12 * frame12ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

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
  rw [powersetCard_fin2]
  simp [volumeWeight_frame12_0, volumeWeight_frame12_1]
  norm_num

end SmallInstance
end StructuredColumnSelection
