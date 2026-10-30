import StructuredColumnSelection.EqualEnergyPivot
import StructuredColumnSelection.InvTraceGrowth

/-!
# Equal energy does not make the third CPQR pivot agree

On the orthogonal-row frame whose columns are

```
(-3, -4, -2, -2, -1,  0),
(-2, -1,  2,  3,  0, -4),
(-2,  0,  3, -2,  4,  1)
```

divided by `√34`, every column energy is `1/2`. Both rules take column `0`
and then column `2`. After `{0, 2}`, max-residual CPQR takes column `3`
and the increment pivot takes column `5`. The three-column sets differ.

Columns `0` and `2` are not orthogonal, so the orthogonal-block agreement
does not apply. This does not close outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

def pathInt : Fin 3 → Fin 6 → ℤ
  | 0, 0 => -3
  | 0, 1 => -4
  | 0, 2 => -2
  | 0, 3 => -2
  | 0, 4 => -1
  | 0, 5 => 0
  | 1, 0 => -2
  | 1, 1 => -1
  | 1, 2 => 2
  | 1, 3 => 3
  | 1, 4 => 0
  | 1, 5 => -4
  | 2, 0 => -2
  | 2, 1 => 0
  | 2, 2 => 3
  | 2, 3 => -2
  | 2, 4 => 4
  | 2, 5 => 1

noncomputable def pathFrame : Matrix (Fin 3) (Fin 6) ℝ :=
  fun i j => (pathInt i j : ℝ) / Real.sqrt 34

def pathJ : Finset (Fin 6) := {0, 2}

noncomputable def pathGram2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((1 : ℝ) / 2), (-2) / 17; (-2) / 17, 1 / 2]

noncomputable def pathInv2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((578 : ℝ) / 273), 136 / 273; 136 / 273, 578 / 273]

lemma path_mul (a b : ℤ) :
    ((a : ℝ) / Real.sqrt 34) * ((b : ℝ) / Real.sqrt 34) =
      ((a * b : ℤ) : ℝ) / 34 := by
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 34),
    ← Int.cast_mul]

lemma pathJ_card : pathJ.card = 2 := by
  have h0 : (0 : Fin 6) ∉ ({2} : Finset (Fin 6)) := by simp
  simp [pathJ, h0, card_insert_of_notMem, card_singleton]

lemma pathJ_pos : pathJ.Nonempty := ⟨0, by simp [pathJ]⟩

lemma pathJ_min : pathJ.min' pathJ_pos = 0 := by
  rw [min'_eq_iff]
  refine ⟨by simp [pathJ], ?_⟩
  intro b hb
  simp only [pathJ, mem_insert, mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact le_rfl
  · exact Fin.zero_le _

lemma pathJ_max : pathJ.max' pathJ_pos = 2 := by
  rw [max'_eq_iff]
  refine ⟨by simp [pathJ], ?_⟩
  intro b hb
  simp only [pathJ, mem_insert, mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact Fin.zero_le _
  · exact le_rfl

lemma path_emb0 :
    pathJ.orderEmbOfFin rfl (finCongr pathJ_card.symm (0 : Fin 2)) = 0 := by
  have hidx :
      finCongr pathJ_card.symm (0 : Fin 2) =
        ⟨0, by rw [pathJ_card]; exact Nat.zero_lt_two⟩ := by
    apply Fin.ext
    simp [finCongr, Fin.cast]
  rw [hidx, orderEmbOfFin_zero]
  exact pathJ_min

lemma path_emb1 :
    pathJ.orderEmbOfFin rfl (finCongr pathJ_card.symm (1 : Fin 2)) = 2 := by
  have hidx :
      finCongr pathJ_card.symm (1 : Fin 2) =
        ⟨pathJ.card - 1, Nat.sub_lt (by rw [pathJ_card]; exact Nat.zero_lt_two)
          (Nat.succ_pos 0)⟩ := by
    apply Fin.ext
    simp [finCongr, Fin.cast, pathJ_card]
  have hz : 0 < pathJ.card := by
    rw [pathJ_card]
    exact Nat.zero_lt_two
  rw [hidx, orderEmbOfFin_last (hz := hz)]
  exact pathJ_max

lemma pathFrame_orthogonal : OrthogonalRows pathFrame := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six,
      pathFrame, one_apply] <;>
    rw [path_mul, path_mul, path_mul, path_mul, path_mul, path_mul] <;>
    simp [pathInt] <;>
    norm_num

lemma path_inner (j1 j2 : Fin 6) :
    colInner pathFrame j1 j2 =
      ((pathInt 0 j1 * pathInt 0 j2 + pathInt 1 j1 * pathInt 1 j2 +
        pathInt 2 j1 * pathInt 2 j2 : ℤ) : ℝ) / 34 := by
  simp only [colInner, Fin.sum_univ_three, pathFrame]
  rw [path_mul, path_mul, path_mul, ← add_div, ← add_div, ← Int.cast_add, ← Int.cast_add]

lemma path_energy (j : Fin 6) : colInner pathFrame j j = (1 : ℝ) / 2 := by
  fin_cases j <;> rw [path_inner] <;> simp [pathInt] <;> norm_num

lemma path_inner_01 : colInner pathFrame 0 1 = (7 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_02 : colInner pathFrame 0 2 = (-2 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_03 : colInner pathFrame 0 3 = (2 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_04 : colInner pathFrame 0 4 = (-5 : ℝ) / 34 := by
  rw [path_inner]; simp [pathInt]

lemma path_inner_05 : colInner pathFrame 0 5 = (3 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_21 : colInner pathFrame 2 1 = (3 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_23 : colInner pathFrame 2 3 = (2 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_24 : colInner pathFrame 2 4 = (7 : ℝ) / 17 := by
  rw [path_inner]; simp [pathInt]; norm_num

lemma path_inner_25 : colInner pathFrame 2 5 = (-5 : ℝ) / 34 := by
  rw [path_inner]; simp [pathInt]

lemma path_res_empty (j : Fin 6) : residualSq pathFrame ∅ j = (1 : ℝ) / 2 := by
  rw [← colInner_eq_residualSq, path_energy]

lemma path_max_empty : maxResidual pathFrame ∅ = (1 : ℝ) / 2 := by
  have hunused : (unused (∅ : Finset (Fin 6))).Nonempty := ⟨0, by simp [unused_empty]⟩
  unfold maxResidual
  rw [dif_pos hunused]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j _
    rw [path_res_empty]
  · rw [le_sup'_iff]
    refine ⟨0, by simp [unused_empty], ?_⟩
    rw [path_res_empty]

lemma path_cpqr_empty : cpqrPivot pathFrame ∅ = some 0 := by
  simp only [cpqrPivot]
  have h0 : (0 : Fin 6) ∈ (unused (∅ : Finset (Fin 6))).filter fun j =>
      residualSq pathFrame ∅ j = maxResidual pathFrame ∅ ∧
        0 < residualSq pathFrame ∅ j := by
    refine mem_filter.mpr ⟨by simp [unused_empty], ?_⟩
    refine ⟨?_, ?_⟩
    · rw [path_res_empty, path_max_empty]
    · rw [path_res_empty]; norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h0, ?_⟩
    intro j _
    exact Fin.zero_le j
  · exact absurd ⟨0, h0⟩ hs

lemma path_empty_det : (selectedColGram pathFrame (∅ : Finset (Fin 6))).det = 1 :=
  Matrix.det_eq_one_of_card_eq_zero (by
    change Fintype.card (Fin 0) = 0
    exact Fintype.card_fin 0)

lemma path_empty_coeff (j : Fin 6) :
    (((selectedColGram pathFrame ∅)⁻¹ *ᵥ
        ((selectedCols pathFrame ∅)ᵀ *ᵥ fun i => pathFrame i j)) ⬝ᵥ
      ((selectedColGram pathFrame ∅)⁻¹ *ᵥ
        ((selectedCols pathFrame ∅)ᵀ *ᵥ fun i => pathFrame i j))) = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hp : (p : ℕ) < 0 := by
    simpa [Finset.card_empty] using p.isLt
  exact absurd hp (Nat.not_lt_zero _)

lemma path_empty_ratio (j : Fin 6) : incrementRatio pathFrame ∅ j = 2 := by
  unfold incrementRatio
  rw [path_empty_coeff, add_zero, path_res_empty]
  norm_num

lemma path_best_empty : incrementBest pathFrame ∅ = 2 := by
  unfold incrementBest
  have h0 : (0 : Fin 6) ∈ incrementCandidates pathFrame ∅ := by
    refine mem_filter.mpr ⟨by simp [unused_empty], ?_⟩
    rw [path_res_empty]
    norm_num
  have hs : (incrementCandidates pathFrame ∅).Nonempty := ⟨0, h0⟩
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [path_empty_ratio] using
      mem_image_of_mem (incrementRatio pathFrame ∅) h0
  · intro r hr
    obtain ⟨j, _, rfl⟩ := mem_image.mp hr
    rw [path_empty_ratio]

lemma path_inc_empty : incrementPivot pathFrame ∅ = some 0 := by
  simp only [incrementPivot]
  rw [if_neg (by rw [path_empty_det]; norm_num)]
  have h0 : (0 : Fin 6) ∈ (incrementCandidates pathFrame ∅).filter fun j =>
      incrementRatio pathFrame ∅ j = incrementBest pathFrame ∅ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨by simp [unused_empty], ?_⟩
      rw [path_res_empty]
      norm_num
    · rw [path_empty_ratio, path_best_empty]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h0, ?_⟩
    intro j _
    exact Fin.zero_le j
  · exact absurd ⟨0, h0⟩ hs

lemma path_equal :
    ∀ i j : Fin 6, colInner pathFrame i i = colInner pathFrame j j := by
  intro i j
  rw [path_energy i, path_energy j]

lemma path_energy_pos : (0 : ℝ) < colInner pathFrame 0 0 := by
  rw [path_energy]
  norm_num

lemma path_res_1 : residualSq pathFrame ({0} : Finset (Fin 6)) 1 = (93 : ℝ) / 578 := by
  rw [singleton_residual_of_equal_energy pathFrame path_equal 0 1 path_energy_pos,
    path_energy, path_inner_01]
  norm_num

lemma path_res_2 : residualSq pathFrame ({0} : Finset (Fin 6)) 2 = (273 : ℝ) / 578 := by
  rw [singleton_residual_of_equal_energy pathFrame path_equal 0 2 path_energy_pos,
    path_energy, path_inner_02]
  norm_num

lemma path_res_3 : residualSq pathFrame ({0} : Finset (Fin 6)) 3 = (273 : ℝ) / 578 := by
  rw [singleton_residual_of_equal_energy pathFrame path_equal 0 3 path_energy_pos,
    path_energy, path_inner_03]
  norm_num

lemma path_res_4 : residualSq pathFrame ({0} : Finset (Fin 6)) 4 = (132 : ℝ) / 289 := by
  rw [singleton_residual_of_equal_energy pathFrame path_equal 0 4 path_energy_pos,
    path_energy, path_inner_04]
  norm_num

lemma path_res_5 : residualSq pathFrame ({0} : Finset (Fin 6)) 5 = (253 : ℝ) / 578 := by
  rw [singleton_residual_of_equal_energy pathFrame path_equal 0 5 path_energy_pos,
    path_energy, path_inner_05]
  norm_num

lemma path_ratio_1 :
    incrementRatio pathFrame ({0} : Finset (Fin 6)) 1 = (970 : ℝ) / 93 := by
  rw [singleton_ratio_of_equal_energy pathFrame path_equal 0 1 path_energy_pos,
    path_energy, path_res_1]
  norm_num

lemma path_ratio_2 :
    incrementRatio pathFrame ({0} : Finset (Fin 6)) 2 = (610 : ℝ) / 273 := by
  rw [singleton_ratio_of_equal_energy pathFrame path_equal 0 2 path_energy_pos,
    path_energy, path_res_2]
  norm_num

lemma path_ratio_3 :
    incrementRatio pathFrame ({0} : Finset (Fin 6)) 3 = (610 : ℝ) / 273 := by
  rw [singleton_ratio_of_equal_energy pathFrame path_equal 0 3 path_energy_pos,
    path_energy, path_res_3]
  norm_num

lemma path_ratio_4 :
    incrementRatio pathFrame ({0} : Finset (Fin 6)) 4 = (157 : ℝ) / 66 := by
  rw [singleton_ratio_of_equal_energy pathFrame path_equal 0 4 path_energy_pos,
    path_energy, path_res_4]
  norm_num

lemma path_ratio_5 :
    incrementRatio pathFrame ({0} : Finset (Fin 6)) 5 = (650 : ℝ) / 253 := by
  rw [singleton_ratio_of_equal_energy pathFrame path_equal 0 5 path_energy_pos,
    path_energy, path_res_5]
  norm_num

lemma path_unused_one (j : Fin 6) (hj : j ∈ unused ({0} : Finset (Fin 6))) :
    j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  fin_cases j
  · simp [unused] at hj
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

lemma path_max_one : maxResidual pathFrame ({0} : Finset (Fin 6)) = (273 : ℝ) / 578 := by
  have hunused : (unused ({0} : Finset (Fin 6))).Nonempty := ⟨2, by simp [unused]⟩
  unfold maxResidual
  rw [dif_pos hunused]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j hj
    rcases path_unused_one j hj with rfl | rfl | rfl | rfl | rfl
    · rw [path_res_1]; norm_num
    · rw [path_res_2]
    · rw [path_res_3]
    · rw [path_res_4]; norm_num
    · rw [path_res_5]; norm_num
  · rw [le_sup'_iff]
    refine ⟨2, by simp [unused], ?_⟩
    rw [path_res_2]

lemma path_cpqr_one : cpqrPivot pathFrame ({0} : Finset (Fin 6)) = some 2 := by
  simp only [cpqrPivot]
  have h2 : (2 : Fin 6) ∈ (unused ({0} : Finset (Fin 6))).filter fun j =>
      residualSq pathFrame ({0} : Finset (Fin 6)) j =
        maxResidual pathFrame ({0} : Finset (Fin 6)) ∧
        0 < residualSq pathFrame ({0} : Finset (Fin 6)) j := by
    refine mem_filter.mpr ⟨by simp [unused], ?_⟩
    refine ⟨?_, ?_⟩
    · rw [path_res_2, path_max_one]
    · rw [path_res_2]; norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h2, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2.1
    have hun := (mem_filter.mp hj).1
    rcases path_unused_one j hun with rfl | rfl | rfl | rfl | rfl
    · rw [path_res_1, path_max_one] at hr
      norm_num at hr
    · exact le_rfl
    · decide
    · rw [path_res_4, path_max_one] at hr
      norm_num at hr
    · rw [path_res_5, path_max_one] at hr
      norm_num at hr
  · exact absurd ⟨2, h2⟩ hs

lemma path_best_one : incrementBest pathFrame ({0} : Finset (Fin 6)) = (610 : ℝ) / 273 := by
  unfold incrementBest
  have h2 : (2 : Fin 6) ∈ incrementCandidates pathFrame ({0} : Finset (Fin 6)) := by
    refine mem_filter.mpr ⟨by simp [unused], ?_⟩
    rw [path_res_2]
    norm_num
  have hs : (incrementCandidates pathFrame ({0} : Finset (Fin 6))).Nonempty := ⟨2, h2⟩
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [path_ratio_2] using
      mem_image_of_mem (incrementRatio pathFrame ({0} : Finset (Fin 6))) h2
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    have hun := (mem_filter.mp hj).1
    rcases path_unused_one j hun with rfl | rfl | rfl | rfl | rfl
    · rw [path_ratio_1]; norm_num
    · rw [path_ratio_2]
    · rw [path_ratio_3]
    · rw [path_ratio_4]; norm_num
    · rw [path_ratio_5]; norm_num

lemma path_inc_one : incrementPivot pathFrame ({0} : Finset (Fin 6)) = some 2 := by
  simp only [incrementPivot]
  have hdet : (selectedColGram pathFrame ({0} : Finset (Fin 6))).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero pathFrame 0 (by
      rw [← colInner_eq_residualSq]
      exact path_energy_pos)
  rw [if_neg hdet]
  have h2 : (2 : Fin 6) ∈
      (incrementCandidates pathFrame ({0} : Finset (Fin 6))).filter fun j =>
        incrementRatio pathFrame ({0} : Finset (Fin 6)) j =
          incrementBest pathFrame ({0} : Finset (Fin 6)) := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨by simp [unused], ?_⟩
      rw [path_res_2]
      norm_num
    · rw [path_ratio_2, path_best_one]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h2, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2
    have hun := (mem_filter.mp (mem_filter.mp hj).1).1
    rcases path_unused_one j hun with rfl | rfl | rfl | rfl | rfl
    · rw [path_ratio_1, path_best_one] at hr
      norm_num at hr
    · exact le_rfl
    · decide
    · rw [path_ratio_4, path_best_one] at hr
      norm_num at hr
    · rw [path_ratio_5, path_best_one] at hr
      norm_num at hr
  · exact absurd ⟨2, h2⟩ hs

lemma path_gram_cast :
    (selectedColGram pathFrame pathJ).submatrix
        (finCongr pathJ_card.symm) (finCongr pathJ_card.symm) = pathGram2 := by
  ext i j
  rw [Matrix.submatrix_apply, selectedColGram_apply_inner]
  fin_cases i <;> fin_cases j <;> dsimp
  · rw [path_emb0, path_energy]
    simp [pathGram2]
  · rw [path_emb0, path_emb1, path_inner_02]
    simp [pathGram2]
  · rw [path_emb1, path_emb0]
    have hcomm : colInner pathFrame 2 0 = colInner pathFrame 0 2 := by
      simp [colInner, mul_comm]
    rw [hcomm, path_inner_02]
    simp [pathGram2]
  · rw [path_emb1, path_energy]
    simp [pathGram2]

lemma path_det : (selectedColGram pathFrame pathJ).det = (273 : ℝ) / 1156 := by
  rw [← Matrix.det_submatrix_equiv_self (finCongr pathJ_card.symm), path_gram_cast,
    Matrix.det_fin_two]
  simp [pathGram2]
  norm_num

lemma path_det_ne : (selectedColGram pathFrame pathJ).det ≠ 0 := by
  rw [path_det]
  norm_num

lemma path_inv_cast :
    ((selectedColGram pathFrame pathJ)⁻¹).submatrix
        (finCongr pathJ_card.symm) (finCongr pathJ_card.symm) = pathInv2 := by
  rw [← Matrix.inv_submatrix_equiv, path_gram_cast]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, pathGram2, pathInv2] <;>
    norm_num

lemma path_coeff (j : Fin 6) (p : Fin 2) :
    ((selectedCols pathFrame pathJ)ᵀ *ᵥ fun i => pathFrame i j)
        (finCongr pathJ_card.symm p) =
      colInner pathFrame
        (pathJ.orderEmbOfFin rfl (finCongr pathJ_card.symm p)) j := by
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, selectedCols,
    Matrix.submatrix_apply, colInner, id_eq]

lemma path_quad (j : Fin 6) (c0 c1 q score : ℝ)
    (h0 : colInner pathFrame 0 j = c0) (h1 : colInner pathFrame 2 j = c1)
    (hq : c0 * (pathInv2 0 0 * c0 + pathInv2 0 1 * c1) +
        c1 * (pathInv2 1 0 * c0 + pathInv2 1 1 * c1) = q)
    (hs : (pathInv2 0 0 * c0 + pathInv2 0 1 * c1) ^ 2 +
        (pathInv2 1 0 * c0 + pathInv2 1 1 * c1) ^ 2 = score) :
    residualSq pathFrame pathJ j = (1 : ℝ) / 2 - q ∧
      incrementRatio pathFrame pathJ j = (1 + score) / ((1 : ℝ) / 2 - q) := by
  let e := finCongr pathJ_card.symm
  let w := (selectedCols pathFrame pathJ)ᵀ *ᵥ fun i => pathFrame i j
  let G := selectedColGram pathFrame pathJ
  have hw0 : w (e 0) = c0 := by
    simpa [w, e, path_emb0] using (path_coeff j 0).trans (by rw [path_emb0, h0])
  have hw1 : w (e 1) = c1 := by
    simpa [w, e, path_emb1] using (path_coeff j 1).trans (by rw [path_emb1, h1])
  have hentry (a b : Fin 2) : G⁻¹ (e a) (e b) = pathInv2 a b := by
    simpa [e, Matrix.submatrix_apply] using congr_fun (congr_fun path_inv_cast a) b
  have hmul0 : (G⁻¹ *ᵥ w) (e 0) = pathInv2 0 0 * c0 + pathInv2 0 1 * c1 := by
    rw [Matrix.mulVec, dotProduct]
    have hsum :=
      (Fintype.sum_equiv e
        (fun p : Fin 2 => G⁻¹ (e 0) (e p) * w (e p))
        (fun t => G⁻¹ (e 0) t * w t) (fun _ => rfl)).symm
    rw [hsum, Fin.sum_univ_two, hentry 0 0, hentry 0 1, hw0, hw1]
  have hmul1 : (G⁻¹ *ᵥ w) (e 1) = pathInv2 1 0 * c0 + pathInv2 1 1 * c1 := by
    rw [Matrix.mulVec, dotProduct]
    have hsum :=
      (Fintype.sum_equiv e
        (fun p : Fin 2 => G⁻¹ (e 1) (e p) * w (e p))
        (fun t => G⁻¹ (e 1) t * w t) (fun _ => rfl)).symm
    rw [hsum, Fin.sum_univ_two, hentry 1 0, hentry 1 1, hw0, hw1]
  have hq' : w ⬝ᵥ (G⁻¹ *ᵥ w) = q := by
    rw [dotProduct]
    have hsum :=
      (Fintype.sum_equiv e
        (fun p : Fin 2 => w (e p) * (G⁻¹ *ᵥ w) (e p))
        (fun t => w t * (G⁻¹ *ᵥ w) t) (fun _ => rfl)).symm
    rw [hsum, Fin.sum_univ_two, hw0, hw1, hmul0, hmul1, hq]
  have hs' : (G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w) = score := by
    rw [dotProduct]
    have hsum :=
      (Fintype.sum_equiv e
        (fun p : Fin 2 => (G⁻¹ *ᵥ w) (e p) * (G⁻¹ *ᵥ w) (e p))
        (fun t => (G⁻¹ *ᵥ w) t * (G⁻¹ *ᵥ w) t) (fun _ => rfl)).symm
    rw [hsum, Fin.sum_univ_two, hmul0, hmul1, ← pow_two, ← pow_two, hs]
  have hres : residualSq pathFrame pathJ j = (1 : ℝ) / 2 - q := by
    rw [residualSq_eq_schur pathFrame pathJ j path_det_ne]
    have hdot : (fun i => pathFrame i j) ⬝ᵥ (fun i => pathFrame i j) =
        colInner pathFrame j j := by
      simp [dotProduct, colInner]
    rw [hdot, path_energy j]
    have hproj := hq'
    simp only [w, G] at hproj
    rw [hproj]
  refine ⟨hres, ?_⟩
  unfold incrementRatio
  have hscore := hs'
  simp only [w, G] at hscore
  rw [hscore, hres]

lemma path_pair_1 :
    residualSq pathFrame pathJ 1 = (25 : ℝ) / 9282 ∧
      incrementRatio pathFrame pathJ 1 = 5716658 / 6825 := by
  have h := path_quad 1 (7 / 17) (3 / 17) (2308 / 4641) (93608 / 74529)
    path_inner_01 path_inner_21 (by simp [pathInv2]; norm_num)
    (by simp [pathInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma path_pair_3 :
    residualSq pathFrame pathJ 3 = (189 : ℝ) / 442 ∧
      incrementRatio pathFrame pathJ 3 = 2278 / 819 := by
  have h := path_quad 3 (2 / 17) (2 / 17) (16 / 221) (32 / 169)
    path_inner_03 path_inner_23 (by simp [pathInv2]; norm_num)
    (by simp [pathInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma path_pair_4 :
    residualSq pathFrame pathJ 4 = (722 : ℝ) / 4641 ∧
      incrementRatio pathFrame pathJ 4 = 1044599 / 98553 := by
  have h := path_quad 4 ((-5) / 34) (7 / 17) (3197 / 9282) (48365 / 74529)
    path_inner_04 path_inner_24 (by simp [pathInv2]; norm_num)
    (by simp [pathInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma path_pair_5 :
    residualSq pathFrame pathJ 5 = (1922 : ℝ) / 4641 ∧
      incrementRatio pathFrame pathJ 5 = 722279 / 262353 := by
  have h := path_quad 5 (3 / 17) ((-5) / 34) (797 / 9282) (10445 / 74529)
    path_inner_05 path_inner_25 (by simp [pathInv2]; norm_num)
    (by simp [pathInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma path_unused_pair (j : Fin 6) (hj : j ∈ unused pathJ) :
    j = 1 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  fin_cases j
  · simp [unused, pathJ] at hj
  · exact Or.inl rfl
  · simp [unused, pathJ] at hj
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

lemma path_max_pair : maxResidual pathFrame pathJ = (189 : ℝ) / 442 := by
  have hunused : (unused pathJ).Nonempty := ⟨3, by simp [unused, pathJ]⟩
  unfold maxResidual
  rw [dif_pos hunused]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j hj
    rcases path_unused_pair j hj with rfl | rfl | rfl | rfl
    · rw [path_pair_1.1]; norm_num
    · rw [path_pair_3.1]
    · rw [path_pair_4.1]; norm_num
    · rw [path_pair_5.1]; norm_num
  · rw [le_sup'_iff]
    refine ⟨3, by simp [unused, pathJ], ?_⟩
    rw [path_pair_3.1]

lemma path_cpqr_pair : cpqrPivot pathFrame pathJ = some 3 := by
  simp only [cpqrPivot]
  have h3 : (3 : Fin 6) ∈ (unused pathJ).filter fun j =>
      residualSq pathFrame pathJ j = maxResidual pathFrame pathJ ∧
        0 < residualSq pathFrame pathJ j := by
    refine mem_filter.mpr ⟨by simp [unused, pathJ], ?_⟩
    refine ⟨?_, ?_⟩
    · rw [path_pair_3.1, path_max_pair]
    · rw [path_pair_3.1]; norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h3, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2.1
    have hun := (mem_filter.mp hj).1
    rcases path_unused_pair j hun with rfl | rfl | rfl | rfl
    · rw [path_pair_1.1, path_max_pair] at hr
      norm_num at hr
    · exact le_rfl
    · rw [path_pair_4.1, path_max_pair] at hr
      norm_num at hr
    · rw [path_pair_5.1, path_max_pair] at hr
      norm_num at hr
  · exact absurd ⟨3, h3⟩ hs

lemma path_best_pair : incrementBest pathFrame pathJ = 722279 / 262353 := by
  unfold incrementBest
  have h5 : (5 : Fin 6) ∈ incrementCandidates pathFrame pathJ := by
    refine mem_filter.mpr ⟨by simp [unused, pathJ], ?_⟩
    rw [path_pair_5.1]
    norm_num
  have hs : (incrementCandidates pathFrame pathJ).Nonempty := ⟨5, h5⟩
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [path_pair_5.2] using
      mem_image_of_mem (incrementRatio pathFrame pathJ) h5
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    have hun := (mem_filter.mp hj).1
    rcases path_unused_pair j hun with rfl | rfl | rfl | rfl
    · rw [path_pair_1.2]; norm_num
    · rw [path_pair_3.2]; norm_num
    · rw [path_pair_4.2]; norm_num
    · rw [path_pair_5.2]

lemma path_inc_pair : incrementPivot pathFrame pathJ = some 5 := by
  simp only [incrementPivot]
  rw [if_neg path_det_ne]
  have h5 : (5 : Fin 6) ∈ (incrementCandidates pathFrame pathJ).filter fun j =>
      incrementRatio pathFrame pathJ j = incrementBest pathFrame pathJ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨by simp [unused, pathJ], ?_⟩
      rw [path_pair_5.1]
      norm_num
    · rw [path_pair_5.2, path_best_pair]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h5, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2
    have hun := (mem_filter.mp (mem_filter.mp hj).1).1
    rcases path_unused_pair j hun with rfl | rfl | rfl | rfl
    · rw [path_pair_1.2, path_best_pair] at hr
      norm_num at hr
    · rw [path_pair_3.2, path_best_pair] at hr
      norm_num at hr
    · rw [path_pair_4.2, path_best_pair] at hr
      norm_num at hr
    · exact le_rfl
  · exact absurd ⟨5, h5⟩ hs

lemma path_cpqr_iterate_1 : cpqrIterate pathFrame 1 = {0} := by
  conv_lhs => unfold cpqrIterate
  have h0 : cpqrIterate pathFrame 0 = (∅ : Finset (Fin 6)) := rfl
  rw [h0, path_cpqr_empty]
  rfl

lemma path_cpqr_iterate_2 : cpqrIterate pathFrame 2 = {0, 2} := by
  conv_lhs => unfold cpqrIterate
  rw [path_cpqr_iterate_1, path_cpqr_one]
  decide

lemma path_cpqr_iterate_3 : cpqrIterate pathFrame 3 = {0, 2, 3} := by
  conv_lhs => unfold cpqrIterate
  rw [path_cpqr_iterate_2]
  rw [show ({0, 2} : Finset (Fin 6)) = pathJ from rfl]
  rw [path_cpqr_pair]
  decide

lemma path_cpqr_set : cpqrSet pathFrame = {0, 2, 3} := by
  simpa [cpqrSet] using path_cpqr_iterate_3

lemma path_inc_iterate_1 : incrementIterate pathFrame 1 = {0} := by
  conv_lhs => unfold incrementIterate
  have h0 : incrementIterate pathFrame 0 = (∅ : Finset (Fin 6)) := rfl
  rw [h0, path_inc_empty]
  rfl

lemma path_inc_iterate_2 : incrementIterate pathFrame 2 = {0, 2} := by
  conv_lhs => unfold incrementIterate
  rw [path_inc_iterate_1, path_inc_one]
  decide

lemma path_inc_iterate_3 : incrementIterate pathFrame 3 = {0, 2, 5} := by
  conv_lhs => unfold incrementIterate
  rw [path_inc_iterate_2]
  rw [show ({0, 2} : Finset (Fin 6)) = pathJ from rfl]
  rw [path_inc_pair]
  decide

lemma path_inc_set : incrementSet pathFrame = {0, 2, 5} := by
  simpa [incrementSet] using path_inc_iterate_3

lemma path_sets_ne : cpqrSet pathFrame ≠ incrementSet pathFrame := by
  rw [path_cpqr_set, path_inc_set]
  decide

theorem equal_energy_third_pivot_split :
    OrthogonalRows pathFrame ∧
      (∀ i j : Fin 6, colInner pathFrame i i = colInner pathFrame j j) ∧
        colInner pathFrame 0 2 ≠ 0 ∧
          cpqrPivot pathFrame ∅ = some 0 ∧
            incrementPivot pathFrame ∅ = some 0 ∧
              cpqrPivot pathFrame ({0} : Finset (Fin 6)) = some 2 ∧
                incrementPivot pathFrame ({0} : Finset (Fin 6)) = some 2 ∧
                  cpqrPivot pathFrame pathJ = some 3 ∧
                    incrementPivot pathFrame pathJ = some 5 ∧
                      cpqrSet pathFrame ≠ incrementSet pathFrame := by
  refine ⟨pathFrame_orthogonal, path_equal, ?_, path_cpqr_empty, path_inc_empty,
    path_cpqr_one, path_inc_one, path_cpqr_pair, path_inc_pair, path_sets_ne⟩
  rw [path_inner_02]
  norm_num

end StructuredColumnSelection
