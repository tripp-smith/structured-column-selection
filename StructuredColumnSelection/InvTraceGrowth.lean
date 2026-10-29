import StructuredColumnSelection.BestColumnIncrement
import StructuredColumnSelection.InvTraceStep

/-!
# One-step inverse-trace growth

If a selected block already satisfies the inductive trace bound, some
unused column can be appended so the next bound holds. This is not the
max-residual CPQR pivot, and it is not the finished induction.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

/-- The real recurrence `f ≤ t(n-t+1)/(k-t+1)` is stable under adding the
phase-I average `((n-t) + f - t)/(k-t)`. -/
lemma trace_bound_step {n k t : ℕ} {f : ℝ}
    (ht : t < k)
    (hf : f ≤ (t : ℝ) * ((n : ℝ) - t + 1) / ((k : ℝ) - t + 1)) :
    f + (((n : ℝ) - t) + f - t) / ((k : ℝ) - t) ≤
      ((t : ℝ) + 1) * ((n : ℝ) - t) / ((k : ℝ) - t) := by
  have hd : (0 : ℝ) < (k : ℝ) - t := by
    have : (t : ℝ) < (k : ℝ) := by exact_mod_cast ht
    linarith
  have hd1 : (0 : ℝ) < (k : ℝ) - t + 1 := by linarith
  have hf' : f * ((k : ℝ) - t + 1) ≤ (t : ℝ) * ((n : ℝ) - t + 1) := by
    rwa [le_div_iff₀ hd1] at hf
  have hcomb :
      f * ((k : ℝ) - t) + (((n : ℝ) - t) + f - t) =
        f * ((k : ℝ) - t + 1) + (n : ℝ) - 2 * t := by
    ring
  have hnum :
      f * ((k : ℝ) - t) + (((n : ℝ) - t) + f - t) ≤
        (t : ℝ) * ((n : ℝ) - t + 1) + (n : ℝ) - 2 * t := by
    linarith
  have hpoly :
      (t : ℝ) * ((n : ℝ) - t + 1) + (n : ℝ) - 2 * t =
        ((t : ℝ) + 1) * ((n : ℝ) - t) := by
    ring
  have hd0 : (k : ℝ) - t ≠ 0 := ne_of_gt hd
  calc
    f + (((n : ℝ) - t) + f - t) / ((k : ℝ) - t)
        = (f * ((k : ℝ) - t) + (((n : ℝ) - t) + f - t)) / ((k : ℝ) - t) := by
          field_simp
    _ ≤ ((t : ℝ) * ((n : ℝ) - t + 1) + (n : ℝ) - 2 * t) / ((k : ℝ) - t) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hd)
    _ = ((t : ℝ) + 1) * ((n : ℝ) - t) / ((k : ℝ) - t) := by
          rw [hpoly]

/-- The residual in the pivot score is the Schur complement used by the
inverse-trace update. -/
lemma residualSq_eq_schur {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n)
    (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j =
      (fun i => A i j) ⬝ᵥ (fun i => A i j) -
        (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
          ((selectedColGram A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) := by
  rw [residualSq_eq_quadForm A J j hG]
  have hsub :
      ((1 - selectedProjector A J) *ᵥ fun i => A i j) =
        (fun i => A i j) - (selectedProjector A J *ᵥ fun i => A i j) := by
    rw [sub_mulVec_eq, one_mulVec_eq]
  rw [hsub, dotProduct_sub_eq]
  have hmul :
      selectedProjector A J *ᵥ (fun i => A i j) =
        selectedCols A J *ᵥ ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) := by
    rw [selectedProjector, mulVec_mul_eq, mulVec_mul_eq]
  have hdot :=
    transpose_mulVec_dot (selectedCols A J) (fun i => A i j)
      ((selectedColGram A J)⁻¹ *ᵥ ((selectedCols A J)ᵀ *ᵥ fun i => A i j))
  rw [← hmul] at hdot
  rw [← hdot]

/-- One appended column preserves the inductive inverse-trace bound. -/
theorem inv_trace_growth_step {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1)) :
    ∃ j, j ∉ J ∧
      (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) := by
  obtain ⟨j, hj, hpos, hratio⟩ := best_column_increment_le A hA J hG ht
  have hschur := residualSq_eq_schur A J j hG
  have hs : (fun i => A i j) ⬝ᵥ (fun i => A i j) -
      (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) ≠ 0 := by
    rw [← hschur]
    exact ne_of_gt hpos
  have hG' : ((selectedCols A J)ᵀ * selectedCols A J).det ≠ 0 := by
    simpa [selectedColGram] using hG
  have hupdate :=
    append_inv_trace_increment (selectedCols A J) (fun i => A i j) hG' hs
  have havg :
      ((selectedColGram A J)⁻¹).trace +
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) :=
    trace_bound_step ht hf
  refine ⟨j, hj, ?_⟩
  have hinc :
      (1 + (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) /
        residualSq A J j ≤
      (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
        ((k : ℝ) - J.card) := hratio
  simp only [selectedColGram] at havg
  rw [hupdate]
  have hratio' :
      (1 + (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) /
        ((fun i => A i j) ⬝ᵥ (fun i => A i j) -
          (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
              ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) ≤
      (((n : ℝ) - J.card) + (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace -
          J.card) /
        ((k : ℝ) - J.card) := by
    simpa [selectedColGram, hschur] using hinc
  exact le_trans
    (add_le_add_right hratio'
      (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace) havg

end StructuredColumnSelection
