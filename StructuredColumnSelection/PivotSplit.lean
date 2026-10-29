import StructuredColumnSelection.IncrementSet

/-!
# The increment pivot is not max-residual CPQR

On the orthogonal-row frame

```
(1/4) * [[1, -3, -2, -1, -1],
         [-3, 1, -2, -1, -1]]
```

both rules take column `0` first. The next max residual is `2/5`, shared by
columns `1` and `2`, so CPQR takes `1`. The next increment ratios are
`17/5` and `29/10`, so the increment pivot takes `2`. The selected sets
are `{0, 1}` and `{0, 2}`.

This does not close outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix BigOperators

noncomputable def splitFrame : Matrix (Fin 2) (Fin 5) ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then (1 : ℝ) / 4
      else if j = 1 then -(3 / 4)
      else if j = 2 then -(1 / 2)
      else -(1 / 4)
    else
      if j = 0 then -(3 / 4)
      else if j = 1 then (1 : ℝ) / 4
      else if j = 2 then -(1 / 2)
      else -(1 / 4)

noncomputable def splitRaw (j : Fin 5) : ℝ :=
  splitFrame 0 0 * splitFrame 0 j + splitFrame 1 0 * splitFrame 1 j

noncomputable def splitRecip :
    Matrix (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card))
      (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) ℝ :=
  fun _ _ => 8 / 5

def splitIdx : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card) :=
  ⟨0, by rw [Finset.card_singleton]; exact Nat.zero_lt_one⟩

lemma splitIdx_unique (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    p = splitIdx := by
  have hsub : Subsingleton (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) := by
    rw [Finset.card_singleton]
    infer_instance
  exact @Subsingleton.elim _ hsub p splitIdx

lemma sum_split (f : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card) → ℝ) :
    ∑ p, f p = f splitIdx := by
  refine Finset.sum_eq_single splitIdx ?_ ?_
  · intro p _ hp
    exact absurd (splitIdx_unique p) hp
  · intro hp
    exact False.elim (hp (Finset.mem_univ _))

lemma splitFrame_orthogonal : OrthogonalRows splitFrame := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five, splitFrame] <;>
    norm_num

lemma split_energy (j : Fin 5) :
    residualSq splitFrame ∅ j = splitFrame 0 j ^ 2 + splitFrame 1 j ^ 2 := by
  rw [residualSq_empty, Fin.sum_univ_two]

lemma split_energy_0 : residualSq splitFrame ∅ 0 = 5 / 8 := by
  rw [split_energy]
  simp [splitFrame]
  norm_num

lemma split_energy_1 : residualSq splitFrame ∅ 1 = 5 / 8 := by
  rw [split_energy]
  simp [splitFrame]
  norm_num

lemma split_energy_2 : residualSq splitFrame ∅ 2 = 1 / 2 := by
  rw [split_energy]
  simp [splitFrame]
  norm_num

lemma split_energy_3 : residualSq splitFrame ∅ 3 = 1 / 8 := by
  rw [split_energy]
  simp [splitFrame]
  norm_num

lemma split_energy_4 : residualSq splitFrame ∅ 4 = 1 / 8 := by
  rw [split_energy]
  simp [splitFrame]
  norm_num

lemma split_max_empty : maxResidual splitFrame ∅ = 5 / 8 := by
  unfold maxResidual
  have hne : (unused (∅ : Finset (Fin 5))).Nonempty := by
    rw [unused_empty]
    exact univ_nonempty
  rw [dif_pos hne]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j _
    fin_cases j
    · simp [split_energy_0]
    · simp [split_energy_1]
    · simp [split_energy_2]; norm_num
    · simp [split_energy_3]; norm_num
    · simp [split_energy_4]; norm_num
  · rw [le_sup'_iff]
    refine ⟨0, ?_, ?_⟩
    · simp [unused_empty]
    · simp [split_energy_0]

lemma split_empty_coeff (j : Fin 5) :
    (((selectedColGram splitFrame ∅)⁻¹ *ᵥ
        ((selectedCols splitFrame ∅)ᵀ *ᵥ fun i => splitFrame i j)) ⬝ᵥ
      ((selectedColGram splitFrame ∅)⁻¹ *ᵥ
        ((selectedCols splitFrame ∅)ᵀ *ᵥ fun i => splitFrame i j))) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hp : (p : ℕ) < 0 := by
    simpa [Finset.card_empty] using p.isLt
  exact absurd hp (Nat.not_lt_zero _)

lemma split_empty_ratio (j : Fin 5) :
    incrementRatio splitFrame ∅ j = 1 / residualSq splitFrame ∅ j := by
  unfold incrementRatio
  rw [split_empty_coeff, add_zero]

lemma split_empty_ratio_0 : incrementRatio splitFrame ∅ 0 = 8 / 5 := by
  rw [split_empty_ratio, split_energy_0]
  norm_num

lemma split_empty_ratio_1 : incrementRatio splitFrame ∅ 1 = 8 / 5 := by
  rw [split_empty_ratio, split_energy_1]
  norm_num

lemma split_empty_ratio_2 : incrementRatio splitFrame ∅ 2 = 2 := by
  rw [split_empty_ratio, split_energy_2]
  norm_num

lemma split_empty_ratio_3 : incrementRatio splitFrame ∅ 3 = 8 := by
  rw [split_empty_ratio, split_energy_3]
  norm_num

lemma split_empty_ratio_4 : incrementRatio splitFrame ∅ 4 = 8 := by
  rw [split_empty_ratio, split_energy_4]
  norm_num

lemma split_cpqr_empty : cpqrPivot splitFrame ∅ = some 0 := by
  simp only [cpqrPivot]
  have h0 : (0 : Fin 5) ∈ (unused (∅ : Finset (Fin 5))).filter fun j =>
      residualSq splitFrame ∅ j = maxResidual splitFrame ∅ ∧
        0 < residualSq splitFrame ∅ j := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused_empty]
    · refine ⟨?_, ?_⟩
      · rw [split_energy_0, split_max_empty]
      · rw [split_energy_0]
        norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    exact ⟨h0, fun _ _ => Fin.zero_le _⟩
  · exact absurd ⟨0, h0⟩ hs

lemma split_increment_best_empty : incrementBest splitFrame ∅ = 8 / 5 := by
  unfold incrementBest
  have h0 : (0 : Fin 5) ∈ incrementCandidates splitFrame ∅ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused_empty]
    · rw [split_energy_0]
      norm_num
  have hs : (incrementCandidates splitFrame ∅).Nonempty := ⟨0, h0⟩
  rw [dif_pos hs]
  rw [min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [split_empty_ratio_0] using
      mem_image_of_mem (incrementRatio splitFrame ∅) h0
  intro r hr
  obtain ⟨j, _, rfl⟩ := mem_image.mp hr
  fin_cases j
  · simp [split_empty_ratio_0]
  · simp [split_empty_ratio_1]
  · simp [split_empty_ratio_2]
    norm_num
  · simp [split_empty_ratio_3]
    norm_num
  · simp [split_empty_ratio_4]
    norm_num

lemma split_increment_empty : incrementPivot splitFrame ∅ = some 0 := by
  have hdet : (selectedColGram splitFrame (∅ : Finset (Fin 5))).det ≠ 0 := by
    rw [selectedColGram_empty_det]
    norm_num
  simp only [incrementPivot]
  rw [if_neg hdet]
  have h0 : (0 : Fin 5) ∈ (incrementCandidates splitFrame ∅).filter fun j =>
      incrementRatio splitFrame ∅ j = incrementBest splitFrame ∅ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, ?_⟩
      · simp [unused_empty]
      · rw [split_energy_0]
        norm_num
    · rw [split_empty_ratio_0, split_increment_best_empty]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    exact ⟨h0, fun _ _ => Fin.zero_le _⟩
  · exact absurd ⟨0, h0⟩ hs

lemma split_col (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) (i : Fin 2) :
    selectedCols splitFrame ({0} : Finset (Fin 5)) i p = splitFrame i 0 := by
  simp [selectedCols, Matrix.submatrix_apply, orderEmbOfFin_singleton_apply]

lemma split_gram_val (p q : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    selectedColGram splitFrame ({0} : Finset (Fin 5)) p q = 5 / 8 := by
  rw [selectedColGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, split_col, Fin.sum_univ_two, splitFrame]
  norm_num

lemma split_gram_inv :
    (selectedColGram splitFrame ({0} : Finset (Fin 5)))⁻¹ = splitRecip := by
  apply Matrix.inv_eq_right_inv
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply, sum_split, split_gram_val]
  have hpq : p = q := (splitIdx_unique p).trans (splitIdx_unique q).symm
  simp [splitRecip, hpq]

lemma split_gram_det_ne :
    (selectedColGram splitFrame ({0} : Finset (Fin 5))).det ≠ 0 :=
  selectedColGram_singleton_det_ne_zero splitFrame 0
    (by rw [split_energy_0]; norm_num)

lemma split_bt (j : Fin 5) (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
        fun i => splitFrame i j) p = splitRaw j := by
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, split_col,
    Fin.sum_univ_two, splitRaw]

lemma split_coeff (j : Fin 5) (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    ((selectedColGram splitFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => splitFrame i j)) p =
      (8 / 5) * splitRaw j := by
  rw [Matrix.mulVec_apply_eq_sum, split_gram_inv, sum_split, split_bt]
  simp [splitRecip]

lemma split_schur_dot (j : Fin 5) :
    ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ fun i => splitFrame i j) ⬝ᵥ
      ((selectedColGram splitFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => splitFrame i j)) =
      (8 / 5) * splitRaw j ^ 2 := by
  rw [dotProduct, sum_split, split_coeff, split_bt]
  ring

lemma split_coeff_sq (j : Fin 5) :
    (((selectedColGram splitFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => splitFrame i j)) ⬝ᵥ
      ((selectedColGram splitFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols splitFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => splitFrame i j))) =
      ((8 / 5) * splitRaw j) ^ 2 := by
  rw [dotProduct, sum_split, split_coeff]
  ring

lemma split_res (j : Fin 5) :
    residualSq splitFrame ({0} : Finset (Fin 5)) j =
      splitFrame 0 j ^ 2 + splitFrame 1 j ^ 2 - (8 / 5) * splitRaw j ^ 2 := by
  rw [residualSq_eq_schur _ _ _ split_gram_det_ne, dotProduct, Fin.sum_univ_two,
    split_schur_dot]
  ring

lemma split_res_1 : residualSq splitFrame ({0} : Finset (Fin 5)) 1 = 2 / 5 := by
  rw [split_res]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_res_2 : residualSq splitFrame ({0} : Finset (Fin 5)) 2 = 2 / 5 := by
  rw [split_res]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_res_3 : residualSq splitFrame ({0} : Finset (Fin 5)) 3 = 1 / 10 := by
  rw [split_res]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_res_4 : residualSq splitFrame ({0} : Finset (Fin 5)) 4 = 1 / 10 := by
  rw [split_res]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_max_singleton : maxResidual splitFrame ({0} : Finset (Fin 5)) = 2 / 5 := by
  unfold maxResidual
  have hne : (unused ({0} : Finset (Fin 5))).Nonempty := by
    refine ⟨1, ?_⟩
    simp [unused]
  rw [dif_pos hne]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j hj
    fin_cases j
    · simp [unused, mem_sdiff] at hj
    · simp [split_res_1]
    · simp [split_res_2]
    · simp [split_res_3]
      norm_num
    · simp [split_res_4]
      norm_num
  · rw [le_sup'_iff]
    refine ⟨1, ?_, ?_⟩
    · simp [unused]
    · simp [split_res_1]

lemma split_cpqr_singleton : cpqrPivot splitFrame ({0} : Finset (Fin 5)) = some 1 := by
  simp only [cpqrPivot]
  have h1 : (1 : Fin 5) ∈ (unused ({0} : Finset (Fin 5))).filter fun j =>
      residualSq splitFrame {0} j = maxResidual splitFrame {0} ∧
        0 < residualSq splitFrame {0} j := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused]
    · refine ⟨?_, ?_⟩
      · rw [split_res_1, split_max_singleton]
      · rw [split_res_1]
        norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h1, ?_⟩
    intro b hb
    fin_cases b
    · have hb0 := (mem_filter.mp hb).1
      simp [unused, mem_sdiff] at hb0
    · exact le_rfl
    · decide
    · decide
    · decide
  · exact absurd ⟨1, h1⟩ hs

lemma split_ratio_expr (j : Fin 5) :
    incrementRatio splitFrame ({0} : Finset (Fin 5)) j =
      (1 + ((8 / 5) * splitRaw j) ^ 2) / residualSq splitFrame {0} j := by
  unfold incrementRatio
  rw [split_coeff_sq]

lemma split_ratio_1 : incrementRatio splitFrame ({0} : Finset (Fin 5)) 1 = 17 / 5 := by
  rw [split_ratio_expr, split_res_1]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_ratio_2 : incrementRatio splitFrame ({0} : Finset (Fin 5)) 2 = 29 / 10 := by
  rw [split_ratio_expr, split_res_2]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_ratio_3 : incrementRatio splitFrame ({0} : Finset (Fin 5)) 3 = 52 / 5 := by
  rw [split_ratio_expr, split_res_3]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_ratio_4 : incrementRatio splitFrame ({0} : Finset (Fin 5)) 4 = 52 / 5 := by
  rw [split_ratio_expr, split_res_4]
  simp [splitRaw, splitFrame]
  norm_num

lemma split_singleton_candidate (j : Fin 5) (hj : j ≠ 0)
    (hpos : 0 < residualSq splitFrame ({0} : Finset (Fin 5)) j) :
    j ∈ incrementCandidates splitFrame ({0} : Finset (Fin 5)) := by
  refine mem_filter.mpr ⟨?_, hpos⟩
  simp [unused, mem_sdiff, hj]

lemma split_increment_best_singleton :
    incrementBest splitFrame ({0} : Finset (Fin 5)) = 29 / 10 := by
  unfold incrementBest
  have h2 : (2 : Fin 5) ∈ incrementCandidates splitFrame {0} :=
    split_singleton_candidate 2 (by decide)
      (by rw [split_res_2]; norm_num)
  have hs : (incrementCandidates splitFrame {0}).Nonempty := ⟨2, h2⟩
  rw [dif_pos hs]
  rw [min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [split_ratio_2] using
      mem_image_of_mem (incrementRatio splitFrame {0}) h2
  intro r hr
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
  fin_cases j
  · simp [incrementCandidates, unused, mem_sdiff] at hj
  · simp [split_ratio_1]
    norm_num
  · simp [split_ratio_2]
  · simp [split_ratio_3]
    norm_num
  · simp [split_ratio_4]
    norm_num

lemma split_increment_singleton : incrementPivot splitFrame ({0} : Finset (Fin 5)) = some 2 := by
  simp only [incrementPivot]
  rw [if_neg split_gram_det_ne]
  have h2 : (2 : Fin 5) ∈ (incrementCandidates splitFrame {0}).filter fun j =>
      incrementRatio splitFrame {0} j = incrementBest splitFrame {0} := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact split_singleton_candidate 2 (by decide) (by rw [split_res_2]; norm_num)
    · rw [split_ratio_2, split_increment_best_singleton]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h2, ?_⟩
    intro b hb
    fin_cases b
    · have hb0 := (mem_filter.mp hb).1
      simp [incrementCandidates, unused, mem_sdiff] at hb0
    · exfalso
      have hr := (mem_filter.mp hb).2
      simp [split_ratio_1, split_increment_best_singleton] at hr
      norm_num at hr
    · exact le_rfl
    · decide
    · decide
  · exact absurd ⟨2, h2⟩ hs

lemma split_cpqr_set :
    cpqrSet splitFrame = insert 1 (insert (0 : Fin 5) (∅ : Finset (Fin 5))) := by
  simp only [cpqrSet, cpqrIterate, split_cpqr_empty]
  have hsing : insert (0 : Fin 5) (∅ : Finset (Fin 5)) = {0} := rfl
  rw [hsing, split_cpqr_singleton]

lemma split_increment_set :
    incrementSet splitFrame = insert 2 (insert (0 : Fin 5) (∅ : Finset (Fin 5))) := by
  simp only [incrementSet, incrementIterate, split_increment_empty]
  have hsing : insert (0 : Fin 5) (∅ : Finset (Fin 5)) = {0} := rfl
  rw [hsing, split_increment_singleton]

lemma split_sets_ne : incrementSet splitFrame ≠ cpqrSet splitFrame := by
  intro h
  have hmem : (1 : Fin 5) ∈ cpqrSet splitFrame := by
    rw [split_cpqr_set]
    simp
  have hnot : (1 : Fin 5) ∉ incrementSet splitFrame := by
    rw [split_increment_set]
    simp
  exact hnot (h.symm ▸ hmem)

theorem increment_set_ne_cpqr :
    ∃ A : Matrix (Fin 2) (Fin 5) ℝ,
      OrthogonalRows A ∧ incrementSet A ≠ cpqrSet A :=
  ⟨splitFrame, splitFrame_orthogonal, split_sets_ne⟩

end StructuredColumnSelection
