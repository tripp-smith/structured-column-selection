import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.VolumeWeights

/-!
# First-pivot leverage and the k = 1 CPQR volume bound

Empty residuals sum to `k`, so a first CPQR pivot has leverage at
least `k / n`. For a single orthonormal row that is already the
selected volume: `volumeWeight A (cpqrSet A) ≥ n⁻¹`.

The corresponding inverse magnitude is at most `√n`, which matches
the workshop scale `√(k(n-k+1))` when `k = 1`. This does **not**
give a polynomial inverse-norm bound for general `k`.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-- A first CPQR pivot has leverage at least `k / n`. -/
theorem firstLeverage_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {j : Fin n} (hj : cpqrPivot A ∅ = some j) :
    (k : ℝ) / n ≤ residualSq A ∅ j := by
  have hn : 0 < n := by
    simpa [Fintype.card_fin] using
      (Fintype.card_pos_iff.mpr ⟨j⟩ : 0 < Fintype.card (Fin n))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum := leverageSum A hA
  have hle : ∀ j' : Fin n, residualSq A ∅ j' ≤ residualSq A ∅ j :=
    firstPivot_is_max A hj
  have hbound :
      ∑ j' : Fin n, residualSq A ∅ j' ≤ ∑ _ : Fin n, residualSq A ∅ j :=
    Finset.sum_le_sum fun j' _ => hle j'
  have : (k : ℝ) ≤ n * residualSq A ∅ j := by
    simpa [hsum, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin] using hbound
  exact (div_le_iff₀ hn0).mpr (by rw [mul_comm]; exact this)

lemma volumeWeight_singleton {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (j : Fin n) :
    volumeWeight A {j} = residualSq A ∅ j := by
  have hcard : ({j} : Finset (Fin n)).card = 1 := card_singleton j
  rw [volumeWeight_eq A hcard, residualSq_empty, Matrix.det_fin_one]
  have hentry : colsSubmatrix A {j} hcard 0 0 = A 0 j := by
    simp [colsSubmatrix, Matrix.submatrix_apply]
  rw [hentry]
  have hone : ∑ i : Fin 1, A i j ^ 2 = A 0 j ^ 2 := by
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · intro i _ hi
      exact (hi (Fin.ext (Nat.lt_one_iff.mp i.isLt))).elim
    · intro h
      exact (h (mem_univ 0)).elim
  rw [hone, pow_two]

lemma cpqrSet_eq_singleton_of_k1 {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ j : Fin n, cpqrPivot A ∅ = some j ∧ cpqrSet A = {j} := by
  have hcard := cpqrSet_card_eq A hA
  cases h : cpqrPivot A ∅ with
  | none =>
    have : (cpqrSet A).card = 0 := by
      simp [cpqrSet, cpqrIterate, h]
    omega
  | some j =>
    refine ⟨j, rfl, ?_⟩
    simp [cpqrSet, cpqrIterate, h]

/-- For a single orthonormal row, CPQR selects a maximum-magnitude
entry whose squared size is at least `n⁻¹`. -/
theorem cpqr_k1_volume_ge {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (n : ℝ)⁻¹ ≤ volumeWeight A (cpqrSet A) := by
  obtain ⟨j, hj, hJ⟩ := cpqrSet_eq_singleton_of_k1 A hA
  have hlev := firstLeverage_ge A hA hj
  rw [hJ, volumeWeight_singleton, ← one_div]
  simpa using hlev

end StructuredColumnSelection
