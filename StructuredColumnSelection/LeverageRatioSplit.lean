import StructuredColumnSelection.IncrementSet

/-!
# Leverage ratio `32/13` does not force the second pivots to agree

On the orthogonal-row frame whose columns are the integer vectors

```
(-4, 0, 3, -4, -3) and (-4, -5, -2, 1, 2)
```

divided by `√50`, every column energy lies in `[13/50, 16/25]`. The largest
energy is `16/25` and the smallest is `13/50`, so the leverage ratio is
`32/13`. Both rules take column `0` first. Every remaining residual equals
`1/4`, so max-residual CPQR takes column `1`. The increment ratios are
`89/16`, `65/16`, `73/16`, and `65/16`, so the increment pivot takes
column `2`.

Equal column energy still makes the second pivots agree. This witness only
shows that leverage ratio `32/13` does not. It does not close outcome 1 or
outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix BigOperators

def leverageInt (i : Fin 2) (j : Fin 5) : ℤ :=
  if i = 0 then
    if j = 0 then -4
    else if j = 1 then 0
    else if j = 2 then 3
    else if j = 3 then -4
    else -3
  else
    if j = 0 then -4
    else if j = 1 then -5
    else if j = 2 then -2
    else if j = 3 then 1
    else 2

noncomputable def leverageFrame : Matrix (Fin 2) (Fin 5) ℝ :=
  fun i j => (leverageInt i j : ℝ) / Real.sqrt 50

noncomputable def leverageRaw (j : Fin 5) : ℝ :=
  leverageFrame 0 0 * leverageFrame 0 j + leverageFrame 1 0 * leverageFrame 1 j

def leverageDot (j : Fin 5) : ℤ :=
  leverageInt 0 0 * leverageInt 0 j + leverageInt 1 0 * leverageInt 1 j

noncomputable def leverageRecip :
    Matrix (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card))
      (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) ℝ :=
  fun _ _ => 25 / 16

def leverageIdx : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card) :=
  ⟨0, by rw [Finset.card_singleton]; exact Nat.zero_lt_one⟩

lemma leverageIdx_unique (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    p = leverageIdx := by
  have hsub : Subsingleton (Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) := by
    rw [Finset.card_singleton]
    infer_instance
  exact @Subsingleton.elim _ hsub p leverageIdx

lemma sum_leverage (f : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card) → ℝ) :
    ∑ p, f p = f leverageIdx := by
  refine Finset.sum_eq_single leverageIdx ?_ ?_
  · intro p _ hp
    exact absurd (leverageIdx_unique p) hp
  · intro hp
    exact False.elim (hp (Finset.mem_univ _))

lemma leverage_sq (a : ℤ) :
    ((a : ℝ) / Real.sqrt 50) ^ 2 = (a : ℝ) ^ 2 / 50 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 50)]

lemma leverage_mul (a b : ℤ) :
    ((a : ℝ) / Real.sqrt 50) * ((b : ℝ) / Real.sqrt 50) =
      ((a : ℝ) * (b : ℝ)) / 50 := by
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 50)]

lemma leverageFrame_orthogonal : OrthogonalRows leverageFrame := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_five,
      leverageFrame, one_apply] <;>
    rw [leverage_mul, leverage_mul, leverage_mul, leverage_mul, leverage_mul] <;>
    simp [leverageInt] <;>
    norm_num

lemma leverage_energy (j : Fin 5) :
    residualSq leverageFrame ∅ j =
      ((leverageInt 0 j : ℝ) ^ 2 + (leverageInt 1 j : ℝ) ^ 2) / 50 := by
  rw [residualSq_empty, Fin.sum_univ_two, leverageFrame, leverageFrame, leverage_sq,
    leverage_sq]
  ring

lemma leverage_energy_0 : residualSq leverageFrame ∅ 0 = 16 / 25 := by
  rw [leverage_energy]
  simp [leverageInt]
  norm_num

lemma leverage_energy_1 : residualSq leverageFrame ∅ 1 = 1 / 2 := by
  rw [leverage_energy]
  simp [leverageInt]
  norm_num

lemma leverage_energy_2 : residualSq leverageFrame ∅ 2 = 13 / 50 := by
  rw [leverage_energy]
  simp [leverageInt]
  norm_num

lemma leverage_energy_3 : residualSq leverageFrame ∅ 3 = 17 / 50 := by
  rw [leverage_energy]
  simp [leverageInt]
  norm_num

lemma leverage_energy_4 : residualSq leverageFrame ∅ 4 = 13 / 50 := by
  rw [leverage_energy]
  simp [leverageInt]
  norm_num

lemma leverage_max_empty : maxResidual leverageFrame ∅ = 16 / 25 := by
  unfold maxResidual
  have hne : (unused (∅ : Finset (Fin 5))).Nonempty := by
    rw [unused_empty]
    exact univ_nonempty
  rw [dif_pos hne]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j _
    fin_cases j
    · simp [leverage_energy_0]
    · simp [leverage_energy_1]
      norm_num
    · simp [leverage_energy_2]
      norm_num
    · simp [leverage_energy_3]
      norm_num
    · simp [leverage_energy_4]
      norm_num
  · rw [le_sup'_iff]
    refine ⟨0, ?_, ?_⟩
    · simp [unused_empty]
    · simp [leverage_energy_0]

lemma leverage_empty_coeff (j : Fin 5) :
    (((selectedColGram leverageFrame ∅)⁻¹ *ᵥ
        ((selectedCols leverageFrame ∅)ᵀ *ᵥ fun i => leverageFrame i j)) ⬝ᵥ
      ((selectedColGram leverageFrame ∅)⁻¹ *ᵥ
        ((selectedCols leverageFrame ∅)ᵀ *ᵥ fun i => leverageFrame i j))) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hp : (p : ℕ) < 0 := by
    simpa [Finset.card_empty] using p.isLt
  exact absurd hp (Nat.not_lt_zero _)

lemma leverage_empty_ratio (j : Fin 5) :
    incrementRatio leverageFrame ∅ j = 1 / residualSq leverageFrame ∅ j := by
  unfold incrementRatio
  rw [leverage_empty_coeff, add_zero]

lemma leverage_empty_ratio_0 : incrementRatio leverageFrame ∅ 0 = 25 / 16 := by
  rw [leverage_empty_ratio, leverage_energy_0]
  norm_num

lemma leverage_empty_ratio_1 : incrementRatio leverageFrame ∅ 1 = 2 := by
  rw [leverage_empty_ratio, leverage_energy_1]
  norm_num

lemma leverage_empty_ratio_2 : incrementRatio leverageFrame ∅ 2 = 50 / 13 := by
  rw [leverage_empty_ratio, leverage_energy_2]
  norm_num

lemma leverage_empty_ratio_3 : incrementRatio leverageFrame ∅ 3 = 50 / 17 := by
  rw [leverage_empty_ratio, leverage_energy_3]
  norm_num

lemma leverage_empty_ratio_4 : incrementRatio leverageFrame ∅ 4 = 50 / 13 := by
  rw [leverage_empty_ratio, leverage_energy_4]
  norm_num

lemma leverage_cpqr_empty : cpqrPivot leverageFrame ∅ = some 0 := by
  simp only [cpqrPivot]
  have h0 : (0 : Fin 5) ∈ (unused (∅ : Finset (Fin 5))).filter fun j =>
      residualSq leverageFrame ∅ j = maxResidual leverageFrame ∅ ∧
        0 < residualSq leverageFrame ∅ j := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused_empty]
    · refine ⟨?_, ?_⟩
      · rw [leverage_energy_0, leverage_max_empty]
      · rw [leverage_energy_0]
        norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    exact ⟨h0, fun _ _ => Fin.zero_le _⟩
  · exact absurd ⟨0, h0⟩ hs

lemma leverage_increment_best_empty : incrementBest leverageFrame ∅ = 25 / 16 := by
  unfold incrementBest
  have h0 : (0 : Fin 5) ∈ incrementCandidates leverageFrame ∅ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused_empty]
    · rw [leverage_energy_0]
      norm_num
  have hs : (incrementCandidates leverageFrame ∅).Nonempty := ⟨0, h0⟩
  rw [dif_pos hs]
  rw [min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [leverage_empty_ratio_0] using
      mem_image_of_mem (incrementRatio leverageFrame ∅) h0
  intro r hr
  obtain ⟨j, _, rfl⟩ := mem_image.mp hr
  fin_cases j
  · simp [leverage_empty_ratio_0]
  · simp [leverage_empty_ratio_1]
    norm_num
  · simp [leverage_empty_ratio_2]
    norm_num
  · simp [leverage_empty_ratio_3]
    norm_num
  · simp [leverage_empty_ratio_4]
    norm_num

lemma leverage_increment_empty : incrementPivot leverageFrame ∅ = some 0 := by
  have hdet : (selectedColGram leverageFrame (∅ : Finset (Fin 5))).det ≠ 0 := by
    rw [selectedColGram_empty_det]
    norm_num
  simp only [incrementPivot]
  rw [if_neg hdet]
  have h0 : (0 : Fin 5) ∈ (incrementCandidates leverageFrame ∅).filter fun j =>
      incrementRatio leverageFrame ∅ j = incrementBest leverageFrame ∅ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, ?_⟩
      · simp [unused_empty]
      · rw [leverage_energy_0]
        norm_num
    · rw [leverage_empty_ratio_0, leverage_increment_best_empty]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    exact ⟨h0, fun _ _ => Fin.zero_le _⟩
  · exact absurd ⟨0, h0⟩ hs

lemma leverage_col (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) (i : Fin 2) :
    selectedCols leverageFrame ({0} : Finset (Fin 5)) i p = leverageFrame i 0 := by
  simp [selectedCols, Matrix.submatrix_apply, orderEmbOfFin_singleton_apply]

lemma leverage_gram_val (p q : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    selectedColGram leverageFrame ({0} : Finset (Fin 5)) p q = 16 / 25 := by
  rw [selectedColGram, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, leverage_col, Fin.sum_univ_two, leverageFrame]
  rw [leverage_mul, leverage_mul]
  simp [leverageInt]
  norm_num

lemma leverage_gram_inv :
    (selectedColGram leverageFrame ({0} : Finset (Fin 5)))⁻¹ = leverageRecip := by
  apply Matrix.inv_eq_right_inv
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply, sum_leverage, leverage_gram_val]
  have hpq : p = q := (leverageIdx_unique p).trans (leverageIdx_unique q).symm
  simp [leverageRecip, hpq]

lemma leverage_gram_det_ne :
    (selectedColGram leverageFrame ({0} : Finset (Fin 5))).det ≠ 0 :=
  selectedColGram_singleton_det_ne_zero leverageFrame 0
    (by rw [leverage_energy_0]; norm_num)

lemma leverageRaw_eq (j : Fin 5) :
    leverageRaw j = (leverageDot j : ℝ) / 50 := by
  simp only [leverageRaw, leverageFrame]
  rw [leverage_mul, leverage_mul]
  simp only [leverageDot, Int.cast_add, Int.cast_mul]
  ring

lemma leverage_bt (j : Fin 5) (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
        fun i => leverageFrame i j) p = leverageRaw j := by
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, leverage_col,
    Fin.sum_univ_two, leverageRaw]

lemma leverage_coeff (j : Fin 5) (p : Fin (({(0 : Fin 5)} : Finset (Fin 5)).card)) :
    ((selectedColGram leverageFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => leverageFrame i j)) p =
      (25 / 16) * leverageRaw j := by
  rw [Matrix.mulVec_apply_eq_sum, leverage_gram_inv, sum_leverage, leverage_bt]
  simp [leverageRecip]

lemma leverage_schur_dot (j : Fin 5) :
    ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ fun i => leverageFrame i j) ⬝ᵥ
      ((selectedColGram leverageFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => leverageFrame i j)) =
      (25 / 16) * leverageRaw j ^ 2 := by
  rw [dotProduct, sum_leverage, leverage_coeff, leverage_bt]
  ring

lemma leverage_coeff_sq (j : Fin 5) :
    (((selectedColGram leverageFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => leverageFrame i j)) ⬝ᵥ
      ((selectedColGram leverageFrame ({0} : Finset (Fin 5)))⁻¹ *ᵥ
        ((selectedCols leverageFrame ({0} : Finset (Fin 5)))ᵀ *ᵥ
          fun i => leverageFrame i j))) =
      ((25 / 16) * leverageRaw j) ^ 2 := by
  rw [dotProduct, sum_leverage, leverage_coeff]
  ring

lemma leverage_res (j : Fin 5) :
    residualSq leverageFrame ({0} : Finset (Fin 5)) j =
      leverageFrame 0 j ^ 2 + leverageFrame 1 j ^ 2 - (25 / 16) * leverageRaw j ^ 2 := by
  rw [residualSq_eq_schur _ _ _ leverage_gram_det_ne, dotProduct, Fin.sum_univ_two,
    leverage_schur_dot]
  ring

lemma leverage_res_num (j : Fin 5) :
    residualSq leverageFrame ({0} : Finset (Fin 5)) j =
      ((leverageInt 0 j : ℝ) ^ 2 + (leverageInt 1 j : ℝ) ^ 2) / 50 -
        (25 / 16) * ((leverageDot j : ℝ) / 50) ^ 2 := by
  rw [leverage_res, leverageRaw_eq]
  simp only [leverageFrame, leverage_sq]
  rw [← add_div]

lemma leverage_res_1 : residualSq leverageFrame ({0} : Finset (Fin 5)) 1 = 1 / 4 := by
  rw [leverage_res_num]
  simp [leverageInt, leverageDot]
  norm_num

lemma leverage_res_2 : residualSq leverageFrame ({0} : Finset (Fin 5)) 2 = 1 / 4 := by
  rw [leverage_res_num]
  simp [leverageInt, leverageDot]
  norm_num

lemma leverage_res_3 : residualSq leverageFrame ({0} : Finset (Fin 5)) 3 = 1 / 4 := by
  rw [leverage_res_num]
  simp [leverageInt, leverageDot]
  norm_num

lemma leverage_res_4 : residualSq leverageFrame ({0} : Finset (Fin 5)) 4 = 1 / 4 := by
  rw [leverage_res_num]
  simp [leverageInt, leverageDot]
  norm_num

lemma leverage_max_singleton : maxResidual leverageFrame ({0} : Finset (Fin 5)) = 1 / 4 := by
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
    · simp [leverage_res_1]
    · simp [leverage_res_2]
    · simp [leverage_res_3]
    · simp [leverage_res_4]
  · rw [le_sup'_iff]
    refine ⟨1, ?_, ?_⟩
    · simp [unused]
    · simp [leverage_res_1]

lemma leverage_cpqr_singleton : cpqrPivot leverageFrame ({0} : Finset (Fin 5)) = some 1 := by
  simp only [cpqrPivot]
  have h1 : (1 : Fin 5) ∈ (unused ({0} : Finset (Fin 5))).filter fun j =>
      residualSq leverageFrame {0} j = maxResidual leverageFrame {0} ∧
        0 < residualSq leverageFrame {0} j := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused]
    · refine ⟨?_, ?_⟩
      · rw [leverage_res_1, leverage_max_singleton]
      · rw [leverage_res_1]
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

lemma leverage_ratio_expr (j : Fin 5) :
    incrementRatio leverageFrame ({0} : Finset (Fin 5)) j =
      (1 + ((25 / 16) * leverageRaw j) ^ 2) /
        residualSq leverageFrame {0} j := by
  unfold incrementRatio
  rw [leverage_coeff_sq]

lemma leverage_ratio_1 : incrementRatio leverageFrame ({0} : Finset (Fin 5)) 1 = 89 / 16 := by
  rw [leverage_ratio_expr, leverage_res_1, leverageRaw_eq]
  simp [leverageDot, leverageInt]
  norm_num

lemma leverage_ratio_2 : incrementRatio leverageFrame ({0} : Finset (Fin 5)) 2 = 65 / 16 := by
  rw [leverage_ratio_expr, leverage_res_2, leverageRaw_eq]
  simp [leverageDot, leverageInt]
  norm_num

lemma leverage_ratio_3 : incrementRatio leverageFrame ({0} : Finset (Fin 5)) 3 = 73 / 16 := by
  rw [leverage_ratio_expr, leverage_res_3, leverageRaw_eq]
  simp [leverageDot, leverageInt]
  norm_num

lemma leverage_ratio_4 : incrementRatio leverageFrame ({0} : Finset (Fin 5)) 4 = 65 / 16 := by
  rw [leverage_ratio_expr, leverage_res_4, leverageRaw_eq]
  simp [leverageDot, leverageInt]
  norm_num

lemma leverage_increment_best_singleton :
    incrementBest leverageFrame ({0} : Finset (Fin 5)) = 65 / 16 := by
  unfold incrementBest
  have h2 : (2 : Fin 5) ∈ incrementCandidates leverageFrame {0} := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp [unused]
    · rw [leverage_res_2]
      norm_num
  have hs : (incrementCandidates leverageFrame {0}).Nonempty := ⟨2, h2⟩
  rw [dif_pos hs]
  rw [min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [leverage_ratio_2] using
      mem_image_of_mem (incrementRatio leverageFrame {0}) h2
  intro r hr
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
  fin_cases j
  · simp [incrementCandidates, unused, mem_sdiff] at hj
  · simp [leverage_ratio_1]
    norm_num
  · simp [leverage_ratio_2]
  · simp [leverage_ratio_3]
    norm_num
  · simp [leverage_ratio_4]

lemma leverage_increment_singleton :
    incrementPivot leverageFrame ({0} : Finset (Fin 5)) = some 2 := by
  simp only [incrementPivot]
  rw [if_neg leverage_gram_det_ne]
  have h2 : (2 : Fin 5) ∈ (incrementCandidates leverageFrame {0}).filter fun j =>
      incrementRatio leverageFrame {0} j = incrementBest leverageFrame {0} := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, ?_⟩
      · simp [unused]
      · rw [leverage_res_2]
        norm_num
    · rw [leverage_ratio_2, leverage_increment_best_singleton]
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
      simp [leverage_ratio_1, leverage_increment_best_singleton] at hr
    · exact le_rfl
    · exfalso
      have hr := (mem_filter.mp hb).2
      simp [leverage_ratio_3, leverage_increment_best_singleton] at hr
    · decide
  · exact absurd ⟨2, h2⟩ hs

lemma leverage_cpqr_set :
    cpqrSet leverageFrame = insert 1 (insert (0 : Fin 5) (∅ : Finset (Fin 5))) := by
  simp only [cpqrSet, cpqrIterate, leverage_cpqr_empty]
  have hsing : insert (0 : Fin 5) (∅ : Finset (Fin 5)) = {0} := rfl
  rw [hsing, leverage_cpqr_singleton]

lemma leverage_increment_set :
    incrementSet leverageFrame =
      insert 2 (insert (0 : Fin 5) (∅ : Finset (Fin 5))) := by
  simp only [incrementSet, incrementIterate, leverage_increment_empty]
  have hsing : insert (0 : Fin 5) (∅ : Finset (Fin 5)) = {0} := rfl
  rw [hsing, leverage_increment_singleton]

lemma leverage_sets_ne : incrementSet leverageFrame ≠ cpqrSet leverageFrame := by
  intro h
  have hmem : (1 : Fin 5) ∈ cpqrSet leverageFrame := by
    rw [leverage_cpqr_set]
    simp
  have hnot : (1 : Fin 5) ∉ incrementSet leverageFrame := by
    rw [leverage_increment_set]
    simp
  exact hnot (h.symm ▸ hmem)

lemma leverage_energy_bounds (j : Fin 5) :
    (13 : ℝ) / 50 ≤ residualSq leverageFrame ∅ j ∧
      residualSq leverageFrame ∅ j ≤ (16 : ℝ) / 25 := by
  fin_cases j
  · dsimp
    rw [leverage_energy_0]
    norm_num
  · dsimp
    rw [leverage_energy_1]
    norm_num
  · dsimp
    rw [leverage_energy_2]
    norm_num
  · dsimp
    rw [leverage_energy_3]
    norm_num
  · dsimp
    rw [leverage_energy_4]
    norm_num

theorem leverage_ratio_pivot_split :
    ∃ A : Matrix (Fin 2) (Fin 5) ℝ,
      OrthogonalRows A ∧
        (∀ j : Fin 5, (13 : ℝ) / 50 ≤ residualSq A ∅ j ∧
          residualSq A ∅ j ≤ (16 : ℝ) / 25) ∧
        residualSq A ∅ (0 : Fin 5) = (16 : ℝ) / 25 ∧
        residualSq A ∅ (2 : Fin 5) = (13 : ℝ) / 50 ∧
        ((16 : ℝ) / 25) / ((13 : ℝ) / 50) = 32 / 13 ∧
        incrementSet A ≠ cpqrSet A := by
  refine ⟨leverageFrame, leverageFrame_orthogonal, leverage_energy_bounds, ?_, ?_, ?_,
    leverage_sets_ne⟩
  · exact leverage_energy_0
  · exact leverage_energy_2
  · norm_num

end StructuredColumnSelection
