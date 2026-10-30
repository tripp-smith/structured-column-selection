import StructuredColumnSelection.EqualEnergyPivot
import StructuredColumnSelection.InvTraceGrowth

/-!
# Equal energy does not make every block agree

On the orthogonal-row frame whose columns are

```
(-7, -4, -4, -3, -3, -1),
(-1, -3, -3,  4,  4,  7),
( 0, -5,  5, -5,  5,  0)
```

divided by `10`, every column energy is `1/2`. Columns `0` and `1` have
inner product `31/100`. After that block, max-residual CPQR takes column
`5` and the increment pivot takes column `3`.

Column `5` is orthogonal to column `0`, so this block is not the
two-column CPQR prefix. The one-step agreement for an orthogonal block
does not extend to every equal-energy block. This does not close
outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

def blockInt : Fin 3 → Fin 6 → ℤ
  | 0, 0 => -7
  | 0, 1 => -4
  | 0, 2 => -4
  | 0, 3 => -3
  | 0, 4 => -3
  | 0, 5 => -1
  | 1, 0 => -1
  | 1, 1 => -3
  | 1, 2 => -3
  | 1, 3 => 4
  | 1, 4 => 4
  | 1, 5 => 7
  | 2, 0 => 0
  | 2, 1 => -5
  | 2, 2 => 5
  | 2, 3 => -5
  | 2, 4 => 5
  | 2, 5 => 0

noncomputable def blockFrame : Matrix (Fin 3) (Fin 6) ℝ :=
  fun i j => (blockInt i j : ℝ) / 10

def blockJ : Finset (Fin 6) := {0, 1}

noncomputable def blockGram2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((1 : ℝ) / 2), 31 / 100; 31 / 100, 1 / 2]

noncomputable def blockInv2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((5000 : ℝ) / 1539), -(3100 / 1539); -(3100 / 1539), 5000 / 1539]

lemma blockJ_card : blockJ.card = 2 := by
  have h0 : (0 : Fin 6) ∉ ({1} : Finset (Fin 6)) := by simp
  simp [blockJ, h0, card_insert_of_notMem, card_singleton]

lemma blockJ_pos : blockJ.Nonempty := ⟨0, by simp [blockJ]⟩

lemma blockJ_min : blockJ.min' blockJ_pos = 0 := by
  rw [min'_eq_iff]
  refine ⟨by simp [blockJ], ?_⟩
  intro b hb
  simp only [blockJ, mem_insert, mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact le_rfl
  · exact Fin.zero_le _

lemma blockJ_max : blockJ.max' blockJ_pos = 1 := by
  rw [max'_eq_iff]
  refine ⟨by simp [blockJ], ?_⟩
  intro b hb
  simp only [blockJ, mem_insert, mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact Fin.zero_le _
  · exact le_rfl

lemma block_emb0 :
    blockJ.orderEmbOfFin rfl (finCongr blockJ_card.symm (0 : Fin 2)) = 0 := by
  have hidx :
      finCongr blockJ_card.symm (0 : Fin 2) =
        ⟨0, by rw [blockJ_card]; exact Nat.zero_lt_two⟩ := by
    apply Fin.ext
    simp [finCongr, Fin.cast]
  rw [hidx, orderEmbOfFin_zero]
  exact blockJ_min

lemma block_emb1 :
    blockJ.orderEmbOfFin rfl (finCongr blockJ_card.symm (1 : Fin 2)) = 1 := by
  have hidx :
      finCongr blockJ_card.symm (1 : Fin 2) =
        ⟨blockJ.card - 1, Nat.sub_lt (by rw [blockJ_card]; exact Nat.zero_lt_two)
          (Nat.succ_pos 0)⟩ := by
    apply Fin.ext
    simp [finCongr, Fin.cast, blockJ_card]
  have hz : 0 < blockJ.card := by
    rw [blockJ_card]
    exact Nat.zero_lt_two
  rw [hidx, orderEmbOfFin_last (hz := hz)]
  exact blockJ_max

lemma blockFrame_orthogonal : OrthogonalRows blockFrame := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six,
      blockFrame, blockInt] <;>
    norm_num

lemma block_energy (j : Fin 6) : colInner blockFrame j j = (1 : ℝ) / 2 := by
  fin_cases j <;>
    simp only [colInner, Fin.sum_univ_three, blockFrame, blockInt] <;>
    norm_num

lemma block_inner (j1 j2 : Fin 6) :
    colInner blockFrame j1 j2 =
      ((blockInt 0 j1 * blockInt 0 j2 + blockInt 1 j1 * blockInt 1 j2 +
        blockInt 2 j1 * blockInt 2 j2 : ℤ) : ℝ) / 100 := by
  simp only [colInner, Fin.sum_univ_three, blockFrame]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, ← add_div, ← add_div]
  simp only [← Int.cast_mul, ← Int.cast_add]
  norm_num

lemma block_inner_01 : colInner blockFrame 0 1 = (31 : ℝ) / 100 := by
  rw [block_inner]
  simp [blockInt]

lemma block_inner_02 : colInner blockFrame 0 2 = (31 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_12 : colInner blockFrame 1 2 = 0 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_03 : colInner blockFrame 0 3 = (17 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_13 : colInner blockFrame 1 3 = (25 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_04 : colInner blockFrame 0 4 = (17 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_14 : colInner blockFrame 1 4 = (-25 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_05 : colInner blockFrame 0 5 = 0 := by
  rw [block_inner]; simp [blockInt]

lemma block_inner_15 : colInner blockFrame 1 5 = (-17 : ℝ) / 100 := by
  rw [block_inner]; simp [blockInt]

lemma block_gram_cast :
    (selectedColGram blockFrame blockJ).submatrix
        (finCongr blockJ_card.symm) (finCongr blockJ_card.symm) = blockGram2 := by
  ext i j
  rw [Matrix.submatrix_apply, selectedColGram_apply_inner]
  fin_cases i <;> fin_cases j <;> dsimp
  · rw [block_emb0, block_energy]
    simp [blockGram2]
  · rw [block_emb0, block_emb1, block_inner_01]
    simp [blockGram2]
  · rw [block_emb1, block_emb0]
    have hcomm : colInner blockFrame 1 0 = colInner blockFrame 0 1 := by
      simp [colInner, mul_comm]
    rw [hcomm, block_inner_01]
    simp [blockGram2]
  · rw [block_emb1, block_energy]
    simp [blockGram2]

lemma block_det : (selectedColGram blockFrame blockJ).det = (1539 : ℝ) / 10000 := by
  rw [← Matrix.det_submatrix_equiv_self (finCongr blockJ_card.symm), block_gram_cast,
    Matrix.det_fin_two]
  simp [blockGram2]
  norm_num

lemma block_det_ne : (selectedColGram blockFrame blockJ).det ≠ 0 := by
  rw [block_det]
  norm_num

lemma block_inv_cast :
    ((selectedColGram blockFrame blockJ)⁻¹).submatrix
        (finCongr blockJ_card.symm) (finCongr blockJ_card.symm) = blockInv2 := by
  rw [← Matrix.inv_submatrix_equiv, block_gram_cast]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, blockGram2, blockInv2] <;>
    norm_num

lemma block_coeff (j : Fin 6) (p : Fin 2) :
    ((selectedCols blockFrame blockJ)ᵀ *ᵥ fun i => blockFrame i j)
        (finCongr blockJ_card.symm p) =
      colInner blockFrame
        (blockJ.orderEmbOfFin rfl (finCongr blockJ_card.symm p)) j := by
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, selectedCols,
    Matrix.submatrix_apply, colInner, id_eq]

lemma block_quad (j : Fin 6) (c0 c1 q score : ℝ)
    (h0 : colInner blockFrame 0 j = c0) (h1 : colInner blockFrame 1 j = c1)
    (hq : c0 * (blockInv2 0 0 * c0 + blockInv2 0 1 * c1) +
        c1 * (blockInv2 1 0 * c0 + blockInv2 1 1 * c1) = q)
    (hs : (blockInv2 0 0 * c0 + blockInv2 0 1 * c1) ^ 2 +
        (blockInv2 1 0 * c0 + blockInv2 1 1 * c1) ^ 2 = score) :
    residualSq blockFrame blockJ j = (1 : ℝ) / 2 - q ∧
      incrementRatio blockFrame blockJ j = (1 + score) / ((1 : ℝ) / 2 - q) := by
  let e := finCongr blockJ_card.symm
  let w := (selectedCols blockFrame blockJ)ᵀ *ᵥ fun i => blockFrame i j
  let G := selectedColGram blockFrame blockJ
  have hw0 : w (e 0) = c0 := by
    simpa [w, e, block_emb0] using (block_coeff j 0).trans (by rw [block_emb0, h0])
  have hw1 : w (e 1) = c1 := by
    simpa [w, e, block_emb1] using (block_coeff j 1).trans (by rw [block_emb1, h1])
  have hentry (a b : Fin 2) : G⁻¹ (e a) (e b) = blockInv2 a b := by
    simpa [e, Matrix.submatrix_apply] using congr_fun (congr_fun block_inv_cast a) b
  have hmul0 : (G⁻¹ *ᵥ w) (e 0) = blockInv2 0 0 * c0 + blockInv2 0 1 * c1 := by
    rw [Matrix.mulVec, dotProduct]
    have hsum :=
      (Fintype.sum_equiv e
        (fun p : Fin 2 => G⁻¹ (e 0) (e p) * w (e p))
        (fun t => G⁻¹ (e 0) t * w t) (fun _ => rfl)).symm
    rw [hsum, Fin.sum_univ_two, hentry 0 0, hentry 0 1, hw0, hw1]
  have hmul1 : (G⁻¹ *ᵥ w) (e 1) = blockInv2 1 0 * c0 + blockInv2 1 1 * c1 := by
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
  have hres : residualSq blockFrame blockJ j = (1 : ℝ) / 2 - q := by
    rw [residualSq_eq_schur blockFrame blockJ j block_det_ne]
    have hdot : (fun i => blockFrame i j) ⬝ᵥ (fun i => blockFrame i j) =
        colInner blockFrame j j := by
      simp [dotProduct, colInner]
    rw [hdot, block_energy j]
    have hproj := hq'
    simp only [w, G] at hproj
    rw [hproj]
  refine ⟨hres, ?_⟩
  unfold incrementRatio
  have hscore := hs'
  simp only [w, G] at hscore
  rw [hscore, hres]

lemma block_res_ratio_2 :
    residualSq blockFrame blockJ 2 = (289 : ℝ) / 1539 ∧
      incrementRatio blockFrame blockJ 2 = 5694542 / 444771 := by
  have h := block_quad 2 (31 / 100) 0 (961 / 3078) (3326021 / 2368521)
    block_inner_02 block_inner_12 (by simp [blockInv2]; norm_num)
    (by simp [blockInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma block_res_ratio_3 :
    residualSq blockFrame blockJ 3 = (64 : ℝ) / 171 ∧
      incrementRatio blockFrame blockJ 3 = 321875 / 98496 := by
  have h := block_quad 3 (17 / 100) (25 / 100) (43 / 342) (58706 / 263169)
    block_inner_03 block_inner_13 (by simp [blockInv2]; norm_num)
    (by simp [blockInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma block_res_ratio_4 :
    residualSq blockFrame blockJ 4 = (49 : ℝ) / 1539 ∧
      incrementRatio blockFrame blockJ 4 = 8166875 / 75411 := by
  have h := block_quad 4 (17 / 100) ((-25) / 100) (1441 / 3078) (5798354 / 2368521)
    block_inner_04 block_inner_14 (by simp [blockInv2]; norm_num)
    (by simp [blockInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma block_res_ratio_5 :
    residualSq blockFrame blockJ 5 = (625 : ℝ) / 1539 ∧
      incrementRatio blockFrame blockJ 5 = 5390 / 1539 := by
  have h := block_quad 5 0 ((-17) / 100) (289 / 3078) (1000229 / 2368521)
    block_inner_05 block_inner_15 (by simp [blockInv2]; norm_num)
    (by simp [blockInv2]; norm_num)
  refine ⟨?_, ?_⟩
  · rw [h.1]; norm_num
  · rw [h.2]; norm_num

lemma block_unused_or (j : Fin 6) (hj : j ∈ unused blockJ) :
    j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  fin_cases j
  · simp [unused, blockJ] at hj
  · simp [unused, blockJ] at hj
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

lemma block_max : maxResidual blockFrame blockJ = (625 : ℝ) / 1539 := by
  have hunused : (unused blockJ).Nonempty := ⟨5, by simp [unused, blockJ]⟩
  unfold maxResidual
  rw [dif_pos hunused]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j hj
    rcases block_unused_or j hj with rfl | rfl | rfl | rfl
    · rw [block_res_ratio_2.1]; norm_num
    · rw [block_res_ratio_3.1]; norm_num
    · rw [block_res_ratio_4.1]; norm_num
    · rw [block_res_ratio_5.1]
  · rw [le_sup'_iff]
    refine ⟨5, by simp [unused, blockJ], ?_⟩
    rw [block_res_ratio_5.1]

lemma block_cpqr : cpqrPivot blockFrame blockJ = some 5 := by
  simp only [cpqrPivot]
  have h5 : (5 : Fin 6) ∈ (unused blockJ).filter fun j =>
      residualSq blockFrame blockJ j = maxResidual blockFrame blockJ ∧
        0 < residualSq blockFrame blockJ j := by
    refine mem_filter.mpr ⟨by simp [unused, blockJ], ?_⟩
    refine ⟨?_, ?_⟩
    · rw [block_res_ratio_5.1, block_max]
    · rw [block_res_ratio_5.1]; norm_num
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h5, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2.1
    have hun := (mem_filter.mp hj).1
    rcases block_unused_or j hun with rfl | rfl | rfl | rfl
    · rw [block_res_ratio_2.1, block_max] at hr
      norm_num at hr
    · rw [block_res_ratio_3.1, block_max] at hr
      norm_num at hr
    · rw [block_res_ratio_4.1, block_max] at hr
      norm_num at hr
    · exact le_rfl
  · exact absurd ⟨5, h5⟩ hs

lemma block_best : incrementBest blockFrame blockJ = 321875 / 98496 := by
  unfold incrementBest
  have h3 : (3 : Fin 6) ∈ incrementCandidates blockFrame blockJ := by
    refine mem_filter.mpr ⟨by simp [unused, blockJ], ?_⟩
    rw [block_res_ratio_3.1]
    norm_num
  have hs : (incrementCandidates blockFrame blockJ).Nonempty := ⟨3, h3⟩
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · simpa [block_res_ratio_3.2] using
      mem_image_of_mem (incrementRatio blockFrame blockJ) h3
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    have hun := (mem_filter.mp hj).1
    rcases block_unused_or j hun with rfl | rfl | rfl | rfl
    · rw [block_res_ratio_2.2]; norm_num
    · rw [block_res_ratio_3.2]
    · rw [block_res_ratio_4.2]; norm_num
    · rw [block_res_ratio_5.2]; norm_num

lemma block_increment : incrementPivot blockFrame blockJ = some 3 := by
  simp only [incrementPivot]
  rw [if_neg block_det_ne]
  have h3 : (3 : Fin 6) ∈ (incrementCandidates blockFrame blockJ).filter fun j =>
      incrementRatio blockFrame blockJ j = incrementBest blockFrame blockJ := by
    refine mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_filter.mpr ⟨by simp [unused, blockJ], ?_⟩
      rw [block_res_ratio_3.1]
      norm_num
    · rw [block_res_ratio_3.2, block_best]
  split_ifs with hs
  · congr 1
    rw [min'_eq_iff]
    refine ⟨h3, ?_⟩
    intro j hj
    have hr := (mem_filter.mp hj).2
    have hun := (mem_filter.mp (mem_filter.mp hj).1).1
    rcases block_unused_or j hun with rfl | rfl | rfl | rfl
    · rw [block_res_ratio_2.2, block_best] at hr
      norm_num at hr
    · exact le_rfl
    · rw [block_res_ratio_4.2, block_best] at hr
      norm_num at hr
    · rw [block_res_ratio_5.2, block_best] at hr
      norm_num at hr
  · exact absurd ⟨3, h3⟩ hs

theorem equal_energy_block_pivot_split :
    OrthogonalRows blockFrame ∧
      (∀ i j : Fin 6, colInner blockFrame i i = colInner blockFrame j j) ∧
        colInner blockFrame 0 1 ≠ 0 ∧
          colInner blockFrame 0 5 = 0 ∧
            cpqrPivot blockFrame blockJ = some 5 ∧
              incrementPivot blockFrame blockJ = some 3 := by
  refine ⟨blockFrame_orthogonal, ?_, ?_, block_inner_05, block_cpqr, block_increment⟩
  · intro i j
    rw [block_energy i, block_energy j]
  · rw [block_inner_01]
    norm_num

end StructuredColumnSelection
