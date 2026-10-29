import StructuredColumnSelection.CPQRVolume
import StructuredColumnSelection.InvTraceGrowth

/-!
# Inverse-trace induction for the increment pivot

Starting from the empty block, repeatedly append a column that meets the
increment bound. After `k` steps the selected Gram has inverse trace at
most `k (n - k + 1)`. This is not max-residual CPQR.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma gram_inv_trace_reindex {k t s : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (e : Fin s ≃ Fin t)
    (hG : (Bᵀ * B).det ≠ 0) :
    (((B.submatrix id e)ᵀ * B.submatrix id e)⁻¹).trace =
      ((Bᵀ * B)⁻¹).trace := by
  have hsub :
      (B.submatrix id e)ᵀ * B.submatrix id e = (Bᵀ * B).submatrix e e := by
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  have hP : ((B.submatrix id e)ᵀ * B.submatrix id e).det ≠ 0 := by
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact hG
  let G := Bᵀ * B
  letI iG : Invertible G := invertible_of_det_ne_zero G hG
  letI iSub : Invertible (G.submatrix e e) :=
    invertible_of_det_ne_zero (G.submatrix e e) (by
      rw [← hsub]
      simpa [G] using hP)
  have hinv : ⅟(G.submatrix e e) = (⅟G).submatrix e e :=
    invOf_submatrix_equiv_eq G e e
  calc
    (((B.submatrix id e)ᵀ * B.submatrix id e)⁻¹).trace
        = ((G.submatrix e e)⁻¹).trace := by rw [← hsub]
    _ = (⅟(G.submatrix e e)).trace := by rw [← Matrix.invOf_eq_nonsing_inv]
    _ = ((⅟G).submatrix e e).trace := by rw [hinv]
    _ = (⅟G).trace := trace_submatrix_equiv e (⅟G)
    _ = (G⁻¹).trace := by rw [Matrix.invOf_eq_nonsing_inv]

lemma append_inv_trace_eq_insert {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ J)
    (hdet : ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
        appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0) :
    (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
        appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace =
      ((selectedColGram A (insert j J))⁻¹).trace := by
  have hG : (selectedColGram A (insert j J)).det ≠ 0 := by
    rw [← appendColumn_gram_det_eq_insert A hj]
    exact hdet
  have hre :=
    gram_inv_trace_reindex (selectedCols A (insert j J))
      (appendToInsertEquiv J j hj) (by simpa [selectedColGram] using hG)
  rw [← appendColumn_eq_selectedCols_insert A hj] at hre
  simpa [selectedColGram] using hre

lemma selectedColGram_empty_inv_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) :
    ((selectedColGram A (∅ : Finset (Fin n)))⁻¹).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : (i : ℕ) < 0 := by
    simpa [Finset.card_empty] using i.isLt
  exact absurd hi (Nat.not_lt_zero _)

lemma insert_inv_trace_step {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1)) :
    ∃ j, j ∉ J ∧ (selectedColGram A (insert j J)).det ≠ 0 ∧
      ((selectedColGram A (insert j J))⁻¹).trace ≤
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
  have happ_le :
      (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) := by
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
        (((n : ℝ) - J.card) +
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
      simpa [selectedColGram, hschur] using hinc
    exact le_trans
      (add_le_add_right hratio'
        (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace) havg
  have hmul := residualSq_mul_gram A hj (Or.inr hG)
  have hinsert_det : (selectedColGram A (insert j J)).det ≠ 0 := by
    by_cases h0 : J.card = 0
    · have hmul' :
          residualSq A J j = (selectedColGram A (insert j J)).det := by
        simpa [h0] using hmul
      rw [← hmul']
      exact ne_of_gt hpos
    · have hmul' :
          residualSq A J j * (selectedColGram A J).det =
            (selectedColGram A (insert j J)).det := by
        simpa [h0] using hmul
      rw [← hmul']
      exact mul_ne_zero (ne_of_gt hpos) hG
  have happdet :
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
    rw [appendColumn_gram_det_eq_insert A hj]
    exact hinsert_det
  have heq := append_inv_trace_eq_insert A hj happdet
  refine ⟨j, hj, hinsert_det, ?_⟩
  rw [← heq]
  exact happ_le

lemma minimizing_inv_trace_bounded {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∀ t, t ≤ k → ∃ J : Finset (Fin n), J.card = t ∧
      (selectedColGram A J).det ≠ 0 ∧
      ((selectedColGram A J)⁻¹).trace ≤
        (t : ℝ) * ((n : ℝ) - t + 1) / ((k : ℝ) - t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨∅, Finset.card_empty, ?_, ?_⟩
    · rw [selectedColGram_empty_det]
      norm_num
    · rw [selectedColGram_empty_inv_trace]
      simp
  | succ t ih =>
    intro ht
    obtain ⟨J, hcard, hG, hf⟩ := ih (Nat.le_of_succ_le ht)
    have hlt : J.card < k := by
      rw [hcard]
      exact Nat.lt_of_succ_le ht
    have hfJ : ((selectedColGram A J)⁻¹).trace ≤
        (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1) := by
      simpa [hcard] using hf
    obtain ⟨j, hj, hdet, htr⟩ := insert_inv_trace_step A hA J hG hlt hfJ
    refine ⟨insert j J, ?_, hdet, ?_⟩
    · rw [card_insert_of_notMem hj, hcard]
    · rw [hcard] at htr
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := Nat.cast_succ t
      have hnum : (n : ℝ) - ((t : ℝ) + 1) + 1 = (n : ℝ) - t := by ring
      have hden : (k : ℝ) - ((t : ℝ) + 1) + 1 = (k : ℝ) - t := by ring
      rw [hcast, hnum, hden]
      exact htr

/-- Some `k` columns, chosen by the increment bound, have inverse trace at
most `k (n - k + 1)`. -/
theorem minimizing_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ((selectedColGram A J)⁻¹).trace ≤ (k : ℝ) * ((n : ℝ) - k + 1) := by
  obtain ⟨J, hcard, hG, hf⟩ := minimizing_inv_trace_bounded A hA k le_rfl
  refine ⟨J, hcard, hG, ?_⟩
  have hden : (k : ℝ) - k + 1 = 1 := by ring
  rw [hden, div_one] at hf
  exact hf

end StructuredColumnSelection
