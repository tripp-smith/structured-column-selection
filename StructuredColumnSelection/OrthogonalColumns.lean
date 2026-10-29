import StructuredColumnSelection.StaticClass
import StructuredColumnSelection.IncrementSet

/-!
# CPQR on pairwise orthogonal columns

`ColumnIncoherent A 0` says distinct columns have inner product zero.
Together with orthogonal rows, every column energy is `0` or `1`, and
exactly `k` columns have energy `1`. Max-residual CPQR selects those
columns. Their Gram matrix is the identity, so the inverse trace is `k`
and `‖x‖² = ‖A_J x‖²`.

This is a CPQR bound on a static class read from `A`. It does not close
outcome 3. The adverse family is not incoherent at `0`.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma colInner_comm {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (i j : Fin n) :
    colInner A i j = colInner A j i := by
  simp only [colInner, mul_comm]

lemma colInner_eq_zero_of_incoherent {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hC : ColumnIncoherent A 0)
    {i j : Fin n} (hij : i ≠ j) : colInner A i j = 0 := by
  exact abs_eq_zero.mp (le_antisymm (hC i j hij) (abs_nonneg _))

lemma mulVec_transpose_col {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j m : Fin n) :
    (Aᵀ *ᵥ fun i => A i j) m = colInner A j m := by
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, colInner]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma column_coeff_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (j : Fin n) :
    (Aᵀ *ᵥ fun i => A i j) ⬝ᵥ (Aᵀ *ᵥ fun i => A i j) = colInner A j j := by
  have hAA : A * Aᵀ = 1 := by simpa [OrthogonalRows] using hA
  let a : Fin k → ℝ := fun i => A i j
  calc
    (Aᵀ *ᵥ a) ⬝ᵥ (Aᵀ *ᵥ a) = a ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ a)) :=
      transpose_mulVec_dot A a (Aᵀ *ᵥ a)
    _ = a ⬝ᵥ ((A * Aᵀ) *ᵥ a) := by rw [← mulVec_mul_eq]
    _ = a ⬝ᵥ a := by rw [hAA, one_mulVec_eq]
    _ = colInner A j j := by simp only [dotProduct, colInner, a]

lemma column_coeff_sq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hC : ColumnIncoherent A 0) (j : Fin n) :
    (Aᵀ *ᵥ fun i => A i j) ⬝ᵥ (Aᵀ *ᵥ fun i => A i j) =
      colInner A j j ^ 2 := by
  let a : Fin k → ℝ := fun i => A i j
  have hsingle :
      ∑ m : Fin n, (Aᵀ *ᵥ a) m * (Aᵀ *ᵥ a) m =
        (Aᵀ *ᵥ a) j * (Aᵀ *ᵥ a) j := by
    refine Finset.sum_eq_single j ?_ ?_
    · intro m _ hm
      rw [mulVec_transpose_col]
      rw [colInner_eq_zero_of_incoherent A hC (Ne.symm hm)]
      ring
    · intro hj
      exact (hj (mem_univ j)).elim
  rw [dotProduct, hsingle, mulVec_transpose_col, pow_two]

lemma column_energy_zero_or_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hC : ColumnIncoherent A 0) (j : Fin n) :
    colInner A j j = 0 ∨ colInner A j j = 1 := by
  have heq : colInner A j j ^ 2 = colInner A j j :=
    (column_coeff_sq A hC j).symm.trans (column_coeff_energy A hA j)
  have hmul : colInner A j j * (colInner A j j - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hmul with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

lemma energy_sum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ j : Fin n, colInner A j j = (k : ℝ) := by
  have hAA : A * Aᵀ = 1 := by simpa [OrthogonalRows] using hA
  calc
    ∑ j : Fin n, colInner A j j
        = ∑ j : Fin n, ∑ i : Fin k, A i j * A i j := by simp [colInner]
    _ = ∑ i : Fin k, ∑ j : Fin n, A i j * A i j := by rw [Finset.sum_comm]
    _ = (A * Aᵀ).trace := by
          simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
    _ = (1 : Matrix (Fin k) (Fin k) ℝ).trace := by rw [hAA]
    _ = (k : ℝ) := by simp [Matrix.trace_one, Fintype.card_fin]

/-- Columns of energy `1`. -/
noncomputable def unitColumns {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) :
    Finset (Fin n) :=
  (univ : Finset (Fin n)).filter fun j => colInner A j j = 1

lemma unitColumns_card {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hC : ColumnIncoherent A 0) :
    (unitColumns A).card = k := by
  have hsum := energy_sum A hA
  have hrest : ∑ j ∈ unitColumns A, colInner A j j = ∑ j : Fin n, colInner A j j := by
    refine sum_subset (filter_subset _ univ) ?_
    intro j _ hj
    have hne : colInner A j j ≠ 1 := by
      intro heq
      exact hj (by simp [unitColumns, heq])
    rcases column_energy_zero_or_one A hA hC j with h0 | h1
    · exact h0
    · exact absurd h1 hne
  rw [← hrest] at hsum
  have hone : ∑ j ∈ unitColumns A, colInner A j j =
      ∑ j ∈ unitColumns A, (1 : ℝ) := by
    refine sum_congr rfl fun j hj => ?_
    simpa [unitColumns, mem_filter] using hj
  rw [hone] at hsum
  have hcard : ((unitColumns A).card : ℝ) = ∑ j ∈ unitColumns A, (1 : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_congr rfl fun _ _ => ?_
    simp
  exact_mod_cast hcard.trans hsum

lemma gram_entry {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (p q : Fin J.card) :
    selectedColGram A J p q =
      colInner A (J.orderEmbOfFin rfl p) (J.orderEmbOfFin rfl q) := by
  simp [selectedColGram, selectedCols, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, colInner]

lemma orth_selected_gram_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hC : ColumnIncoherent A 0)
    (J : Finset (Fin n))
    (hunit : ∀ j ∈ J, colInner A j j = 1) :
    selectedColGram A J = 1 := by
  ext p q
  rw [gram_entry, Matrix.one_apply]
  by_cases hpq : p = q
  · rw [hpq, if_pos rfl]
    exact hunit _ (orderEmbOfFin_mem J rfl q)
  · have hne : J.orderEmbOfFin rfl p ≠ J.orderEmbOfFin rfl q :=
      fun h => hpq ((J.orderEmbOfFin rfl).injective h)
    simp [hpq, colInner_eq_zero_of_incoherent A hC hne]

lemma selected_transpose_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hC : ColumnIncoherent A 0)
    (J : Finset (Fin n)) {j : Fin n} (hj : j ∉ J) :
    (selectedCols A J)ᵀ *ᵥ (fun i => A i j) = 0 := by
  ext p
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, Pi.zero_apply,
    selectedCols, Matrix.submatrix_apply]
  have hne : J.orderEmbOfFin rfl p ≠ j :=
    fun h => hj (h ▸ orderEmbOfFin_mem J rfl p)
  simpa [colInner] using colInner_eq_zero_of_incoherent A hC hne

lemma residual_eq_energy_of_orth {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hC : ColumnIncoherent A 0)
    (J : Finset (Fin n)) {j : Fin n} (hj : j ∉ J)
    (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j = colInner A j j := by
  rw [residualSq_eq_schur A J j hG]
  rw [selected_transpose_zero A hC J hj]
  rw [zero_dotProduct, sub_zero]
  simp [colInner, dotProduct]

lemma cpqr_selects_units {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hC : ColumnIncoherent A 0) (t : ℕ) (ht : t ≤ k) :
    (cpqrIterate A t).card = t ∧
      ∀ j ∈ cpqrIterate A t, colInner A j j = 1 := by
  induction t with
  | zero =>
    exact ⟨by simp [cpqrIterate], by simp [cpqrIterate]⟩
  | succ t ih =>
    have ht' : t ≤ k := Nat.le_of_succ_le ht
    have hlt : t < k := Nat.lt_of_succ_le ht
    obtain ⟨hcard, hunit⟩ := ih ht'
    have hgram : selectedColGram A (cpqrIterate A t) = 1 :=
      orth_selected_gram_one A hC _ hunit
    have hdet : (selectedColGram A (cpqrIterate A t)).det ≠ 0 := by
      rw [hgram, Matrix.det_one]
      exact one_ne_zero
    have hnot : ¬ unitColumns A ⊆ cpqrIterate A t := by
      intro hsub
      have hle := card_le_card hsub
      rw [unitColumns_card A hA hC, hcard] at hle
      omega
    obtain ⟨j0, hj0s, hj0out⟩ := not_subset.mp hnot
    have hj0unit : colInner A j0 j0 = 1 := by
      simpa [unitColumns, mem_filter] using hj0s
    have hres0 : residualSq A (cpqrIterate A t) j0 = 1 := by
      rw [residual_eq_energy_of_orth A hC _ hj0out hdet, hj0unit]
    have hne : (unused (cpqrIterate A t)).Nonempty :=
      ⟨j0, by simp [unused, mem_sdiff, hj0out]⟩
    have hmax : maxResidual A (cpqrIterate A t) = 1 := by
      unfold maxResidual
      rw [dif_pos hne]
      apply le_antisymm
      · rw [sup'_le_iff]
        intro j hj
        have hout : j ∉ cpqrIterate A t := (mem_sdiff.mp hj).2
        rw [residual_eq_energy_of_orth A hC _ hout hdet]
        rcases column_energy_zero_or_one A hA hC j with h0 | h1
        · rw [h0]
          norm_num
        · rw [h1]
      · rw [le_sup'_iff]
        refine ⟨j0, ?_, ?_⟩
        · simp [unused, mem_sdiff, hj0out]
        · rw [hres0]
    let s := (unused (cpqrIterate A t)).filter fun j =>
      residualSq A (cpqrIterate A t) j = maxResidual A (cpqrIterate A t) ∧
        0 < residualSq A (cpqrIterate A t) j
    have hs : s.Nonempty := by
      refine ⟨j0, mem_filter.mpr ⟨?_, ?_, ?_⟩⟩
      · simp [unused, mem_sdiff, hj0out]
      · rw [hres0, hmax]
      · rw [hres0]
        norm_num
    have hpivot : cpqrPivot A (cpqrIterate A t) = some (s.min' hs) := by
      simp only [cpqrPivot]
      rw [dif_pos hs]
    have hjunit : colInner A (s.min' hs) (s.min' hs) = 1 := by
      have hmin := min'_mem s hs
      have hres := (mem_filter.mp hmin).2.1
      rw [hmax] at hres
      have hout : s.min' hs ∉ cpqrIterate A t :=
        (mem_sdiff.mp (mem_filter.mp hmin).1).2
      rw [residual_eq_energy_of_orth A hC _ hout hdet] at hres
      exact hres
    have hjout : s.min' hs ∉ cpqrIterate A t := by
      have hmin := min'_mem s hs
      exact (mem_sdiff.mp (mem_filter.mp hmin).1).2
    have hstep : cpqrIterate A (t + 1) = insert (s.min' hs) (cpqrIterate A t) := by
      simp only [cpqrIterate, hpivot]
    refine ⟨?_, ?_⟩
    · rw [hstep, card_insert_of_notMem hjout, hcard]
    · intro i hi
      rw [hstep, mem_insert] at hi
      rcases hi with rfl | hi
      · exact hjunit
      · exact hunit i hi

theorem incoherent_zero_cpqr_bound {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hC : ColumnIncoherent A 0) :
    (cpqrSet A).card = k ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) := by
  obtain ⟨hcard, hunit⟩ := cpqr_selects_units A hA hC k le_rfl
  have hcard' : (cpqrSet A).card = k := by simpa [cpqrSet] using hcard
  have hgram : selectedColGram A (cpqrSet A) = 1 := by
    change selectedColGram A (cpqrIterate A k) = 1
    exact orth_selected_gram_one A hC (cpqrIterate A k) hunit
  have hdet : (selectedColGram A (cpqrSet A)).det ≠ 0 := by
    rw [hgram, Matrix.det_one]
    exact one_ne_zero
  have htrace : ((selectedColGram A (cpqrSet A))⁻¹).trace = (k : ℝ) := by
    have hinv : (selectedColGram A (cpqrSet A))⁻¹ = 1 := by
      rw [hgram]
      exact Matrix.inv_eq_right_inv (by simp)
    rw [hinv, Matrix.trace_one, Fintype.card_fin, hcard']
  have hnk : k ≤ n := by
    rw [← unitColumns_card A hA hC]
    simpa [Fintype.card_fin] using card_le_univ (unitColumns A)
  have hbound : (k : ℝ) ≤ (k : ℝ) * ((n : ℝ) - k + 1) := by
    have hone : (1 : ℝ) ≤ (n : ℝ) - k + 1 := by
      have : (k : ℝ) ≤ n := by exact_mod_cast hnk
      linarith
    exact le_mul_of_one_le_right (Nat.cast_nonneg k) hone
  refine ⟨hcard', hdet, ?_, ?_⟩
  · rw [htrace]
    exact hbound
  · intro x
    have hBB : (selectedCols A (cpqrSet A))ᵀ * selectedCols A (cpqrSet A) = 1 := by
      simpa [selectedColGram] using hgram
    have henergy : vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) = vecEnergy x := by
      calc
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x)
            = (selectedCols A (cpqrSet A) *ᵥ x) ⬝ᵥ
                (selectedCols A (cpqrSet A) *ᵥ x) :=
          vecEnergy_eq_dot _
        _ = ((selectedCols A (cpqrSet A))ᵀ *ᵥ
                (selectedCols A (cpqrSet A) *ᵥ x)) ⬝ᵥ x :=
          (transpose_mulVec_dot _ _ _).symm
        _ = (((selectedCols A (cpqrSet A))ᵀ *
                selectedCols A (cpqrSet A)) *ᵥ x) ⬝ᵥ x := by
              rw [← mulVec_mul_eq]
        _ = x ⬝ᵥ x := by rw [hBB, one_mulVec_eq]
        _ = vecEnergy x := (vecEnergy_eq_dot x).symm
    have hfac : (1 : ℝ) ≤ 1 + (k : ℝ) * ((n : ℝ) - k) := by
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hnk
      have hdiff : 0 ≤ (n : ℝ) - k := sub_nonneg.mpr hkn
      have : 0 ≤ (k : ℝ) * ((n : ℝ) - k) := mul_nonneg (Nat.cast_nonneg _) hdiff
      linarith
    rw [henergy]
    exact le_mul_of_one_le_left (vecEnergy_nonneg x) hfac

end StructuredColumnSelection
