import StructuredColumnSelection.EqualEnergyPivot

/-!
# Equal energy on an orthogonal column block

If every column has the same energy and the columns already in `J` are
pairwise orthogonal, the selected Gram is a scalar multiple of the
identity. The inverse-trace ratio is then strictly decreasing in the
residual, so max-residual CPQR and the increment pivot return the same
next column.

A one-column block is the agreement half of the equal-energy second
pivot. The same algebra applies to every larger orthogonal block. The
estimate `‖G⁻¹ w‖² ≤ q / λ_min`, fed with the residual lower bound, sits
strictly above the increment average except at this orthogonal endpoint,
so it does not finish a polynomial induction. This lemma does not close
outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma orthogonal_block_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (_hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    selectedColGram A J =
      ((k : ℝ) / n) • (1 : Matrix (Fin J.card) (Fin J.card) ℝ) := by
  let e : ℝ := (k : ℝ) / n
  ext p q
  rw [selectedColGram_apply_inner]
  by_cases hpq : p = q
  · subst hpq
    have hmem : J.orderEmbOfFin rfl p ∈ J := J.orderEmbOfFin_mem rfl p
    simp only [Matrix.smul_apply, Matrix.one_apply]
    simpa [e] using equal_column_energy A hA hE hn (J.orderEmbOfFin rfl p)
  · have hne : J.orderEmbOfFin rfl p ≠ J.orderEmbOfFin rfl q := by
      intro h
      exact hpq ((J.orderEmbOfFin rfl).injective h)
    have hzero := horth (J.orderEmbOfFin rfl p) (J.orderEmbOfFin_mem rfl p)
      (J.orderEmbOfFin rfl q) (J.orderEmbOfFin_mem rfl q) hne
    simp only [Matrix.smul_apply, Matrix.one_apply, if_neg hpq, smul_zero]
    exact hzero

lemma orthogonal_block_energy_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (0 : ℝ) < (k : ℝ) / n :=
  div_pos (by exact_mod_cast hk) (by exact_mod_cast hn)

lemma orthogonal_block_det_ne {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    (selectedColGram A J).det ≠ 0 := by
  rw [orthogonal_block_gram A hA hE hk hn J horth, Matrix.det_smul, Matrix.det_one,
    mul_one]
  exact pow_ne_zero _ (ne_of_gt (orthogonal_block_energy_pos hk hn))

lemma orthogonal_block_inv {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    (selectedColGram A J)⁻¹ =
      (((k : ℝ) / n)⁻¹) • (1 : Matrix (Fin J.card) (Fin J.card) ℝ) := by
  let e : ℝ := (k : ℝ) / n
  apply Matrix.inv_eq_right_inv
  rw [orthogonal_block_gram A hA hE hk hn J horth]
  have he : e ≠ 0 := ne_of_gt (orthogonal_block_energy_pos hk hn)
  calc
    (e • (1 : Matrix (Fin J.card) (Fin J.card) ℝ)) * (e⁻¹ • 1)
        = e • ((1 : Matrix (Fin J.card) (Fin J.card) ℝ) * (e⁻¹ • 1)) := by
          rw [Matrix.smul_mul]
    _ = e • (e⁻¹ • ((1 : Matrix (Fin J.card) (Fin J.card) ℝ) * 1)) := by
          rw [Matrix.mul_smul]
    _ = (e * e⁻¹) • (1 : Matrix (Fin J.card) (Fin J.card) ℝ) := by
          rw [smul_smul, Matrix.one_mul]
    _ = (1 : Matrix (Fin J.card) (Fin J.card) ℝ) := by
          rw [mul_inv_cancel₀ he, one_smul]

lemma orthogonal_block_column_dot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    (fun i => A i j) ⬝ᵥ (fun i => A i j) = colInner A j j := by
  simp only [dotProduct, colInner]

lemma orthogonal_block_ratio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0)
    (j : Fin n) (_hpos : 0 < residualSq A J j) :
    incrementRatio A J j =
      (2 * ((k : ℝ) / n) - residualSq A J j) /
        (((k : ℝ) / n) * residualSq A J j) := by
  set e : ℝ := (k : ℝ) / n with hedef
  have he : 0 < e := orthogonal_block_energy_pos hk hn
  set w : Fin J.card → ℝ := (selectedCols A J)ᵀ *ᵥ fun i => A i j with hw
  have hinvw : (selectedColGram A J)⁻¹ *ᵥ w = e⁻¹ • w := by
    rw [orthogonal_block_inv A hA hE hk hn J horth, smul_mulVec, one_mulVec_eq]
  have hq : w ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ w) = e⁻¹ * (w ⬝ᵥ w) := by
    rw [hinvw, dotProduct_smul, smul_eq_mul]
  have hscore :
      ((selectedColGram A J)⁻¹ *ᵥ w) ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ w) =
        e⁻¹ * (e⁻¹ * (w ⬝ᵥ w)) := by
    rw [hinvw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hcol : (fun i => A i j) ⬝ᵥ (fun i => A i j) = e := by
    rw [orthogonal_block_column_dot, equal_column_energy A hA hE hn j, ← hedef]
  have hres : residualSq A J j = e - (w ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ w)) := by
    rw [residualSq_eq_schur A J j (orthogonal_block_det_ne A hA hE hk hn J horth),
      hcol, hw.symm]
  have hq' : w ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ w) = e - residualSq A J j := by
    linarith
  have hscore' :
      ((selectedColGram A J)⁻¹ *ᵥ w) ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ w) =
        (e - residualSq A J j) / e := by
    rw [hscore, ← hq, hq', mul_comm, ← div_eq_mul_inv]
  unfold incrementRatio
  rw [hw.symm, hscore']
  have hdiv : 1 + (e - residualSq A J j) / e =
      (2 * e - residualSq A J j) / e := by
    rw [← div_self (ne_of_gt he), ← add_div]
    rw [div_eq_div_iff (ne_of_gt he) (ne_of_gt he)]
    ring
  rw [hdiv, div_div, hedef]

lemma orthogonal_block_best {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0)
    (hs : (incrementCandidates A J).Nonempty) :
    incrementBest A J =
      (2 * ((k : ℝ) / n) - maxResidual A J) /
        (((k : ℝ) / n) * maxResidual A J) := by
  have hmax := maxResidual_eq_candidate_sup A J hs
  have he : 0 < (k : ℝ) / n := orthogonal_block_energy_pos hk hn
  unfold incrementBest
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup' hs (residualSq A J)
    have hres : residualSq A J j = maxResidual A J := by
      rw [← hjsup, hmax]
    have hpos : 0 < residualSq A J j := (mem_filter.mp hj).2
    have hratio := orthogonal_block_ratio A hA hE hk hn J horth j hpos
    rw [← hres, ← hratio]
    exact mem_image_of_mem _ hj
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    have hpos : 0 < residualSq A J j := (mem_filter.mp hj).2
    have hratio := orthogonal_block_ratio A hA hE hk hn J horth j hpos
    rw [hratio]
    have hle : residualSq A J j ≤ maxResidual A J := by
      rw [hmax, le_sup'_iff]
      exact ⟨j, hj, le_rfl⟩
    have hM : 0 < maxResidual A J := lt_of_lt_of_le hpos hle
    exact residual_ratio_antitone he hpos hM hle

lemma orthogonal_block_filters_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    (incrementCandidates A J).filter (fun j =>
        incrementRatio A J j = incrementBest A J) =
      (unused J).filter (fun j =>
        residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j) := by
  by_cases hs : (incrementCandidates A J).Nonempty
  · ext j
    have hbest := orthogonal_block_best A hA hE hk hn J horth hs
    constructor
    · intro hj
      have he : 0 < (k : ℝ) / n := orthogonal_block_energy_pos hk hn
      have hmem := (mem_filter.mp hj).1
      have hr := (mem_filter.mp hj).2
      have hpos : 0 < residualSq A J j := (mem_filter.mp hmem).2
      have hratio := orthogonal_block_ratio A hA hE hk hn J horth j hpos
      have hle : residualSq A J j ≤ maxResidual A J := by
        rw [maxResidual_eq_candidate_sup A J hs, le_sup'_iff]
        exact ⟨j, hmem, le_rfl⟩
      have hMpos : 0 < maxResidual A J := lt_of_lt_of_le hpos hle
      have heqRatio :
          (2 * ((k : ℝ) / n) - residualSq A J j) /
              (((k : ℝ) / n) * residualSq A J j) =
            (2 * ((k : ℝ) / n) - maxResidual A J) /
              (((k : ℝ) / n) * maxResidual A J) := by
        rw [← hratio, hr, hbest]
      have hres : residualSq A J j = maxResidual A J := by
        refine le_antisymm hle ?_
        by_contra hnot
        have hlt' : residualSq A J j < maxResidual A J :=
          lt_of_le_of_ne hle (fun heq => hnot heq.symm.le)
        exact (ne_of_lt
          (residual_ratio_strict_anti he hpos hMpos hlt')) heqRatio.symm
      exact mem_filter.mpr ⟨(mem_filter.mp hmem).1, hres, hpos⟩
    · intro hj
      have hunused := (mem_filter.mp hj).1
      have hres := (mem_filter.mp hj).2.1
      have hpos := (mem_filter.mp hj).2.2
      have hmem : j ∈ incrementCandidates A J := mem_filter.mpr ⟨hunused, hpos⟩
      have hratio := orthogonal_block_ratio A hA hE hk hn J horth j hpos
      refine mem_filter.mpr ⟨hmem, ?_⟩
      rw [hratio, hbest, hres]
  · have hempty : incrementCandidates A J = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [hempty, filter_empty]
    symm
    refine eq_empty_of_forall_notMem ?_
    intro j hj
    have hpos := (mem_filter.mp hj).2.2
    have hmem : j ∈ incrementCandidates A J :=
      mem_filter.mpr ⟨(mem_filter.mp hj).1, hpos⟩
    simp [hempty] at hmem

theorem equal_energy_orthogonal_block_same_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 0 < k) (hn : 0 < n) (J : Finset (Fin n))
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → colInner A i j = 0) :
    cpqrPivot A J = incrementPivot A J := by
  have hG := orthogonal_block_det_ne A hA hE hk hn J horth
  have hfilter := orthogonal_block_filters_eq A hA hE hk hn J horth
  simp only [cpqrPivot, incrementPivot, if_neg hG]
  rw [hfilter]

end StructuredColumnSelection
