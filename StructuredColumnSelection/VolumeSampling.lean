import StructuredColumnSelection.InverseNormBounds

/-! Reverse volume sampling as a finite deletion kernel.
No random source or Python extraction is assumed by these algebraic identities. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

/-- Total volume of the k-subsets retained inside S. -/
def retainedVolume {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ :=
  ∑ J ∈ S.powersetCard k, volumeWeight A J

lemma retainedVolume_nonneg {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) : 0 ≤ retainedVolume A S :=
  sum_nonneg fun J _ => volumeWeight_nonneg A J


/-- Retained row Gram; zeroing excluded columns avoids any basis reindexing. -/
def retainedGram {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) : Matrix (Fin k) (Fin k) ℝ :=
  fun p q => ∑ j ∈ S, A p j * A q j

private def maskedColumns {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) : Matrix (Fin k) (Fin n) ℝ :=
  fun i j => if j ∈ S then A i j else 0

private lemma masked_volume {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S J : Finset (Fin n)) (hJ : J.card = k) :
    volumeWeight (maskedColumns A S) J = if J ⊆ S then volumeWeight A J else 0 := by
  by_cases hsub : J ⊆ S
  · rw [if_pos hsub, volumeWeight_eq _ hJ, volumeWeight_eq _ hJ]
    congr 2
    ext i p
    have hp := orderEmbOfFin_mem J hJ p
    simp [colsSubmatrix, maskedColumns, hsub hp]
  · rw [if_neg hsub, volumeWeight_eq _ hJ]
    obtain ⟨j, hj, hjS⟩ := not_subset.mp hsub
    have hjimg : j ∈ image (J.orderEmbOfFin hJ) univ := by
      rw [image_orderEmbOfFin_univ]
      exact hj
    obtain ⟨p, _, hp⟩ := mem_image.mp hjimg
    have hz : (colsSubmatrix (maskedColumns A S) J hJ).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero p (by
        intro i
        simp [colsSubmatrix, maskedColumns, hp, hjS])
    rw [hz]
    norm_num

theorem retainedVolume_eq_det_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) :
    retainedVolume A S = (retainedGram A S).det := by
  have hgram : maskedColumns A S * (maskedColumns A S)ᵀ = retainedGram A S := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, maskedColumns, retainedGram]
    have heq : ∀ j : Fin n,
        (if j ∈ S then A p j else 0) * (if j ∈ S then A q j else 0) =
          if j ∈ S then A p j * A q j else 0 := by intro j; split_ifs <;> simp
    simp_rw [heq]
    have hf : (univ : Finset (Fin n)).filter (fun j => j ∈ S) = S := by
      ext j
      simp
    rw [← sum_filter, hf]
  rw [← hgram, ← volumeWeights_sum_eq_det_mul_transpose]
  have hfilter : ((univ : Finset (Fin n)).powersetCard k).filter (fun J => J ⊆ S) =
      S.powersetCard k := by ext J; simp [mem_powersetCard]; tauto
  calc retainedVolume A S
      = ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter (fun J => J ⊆ S),
          volumeWeight A J := by rw [hfilter]; rfl
    _ = ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
          volumeWeight (maskedColumns A S) J := by
      rw [sum_filter]
      apply sum_congr rfl
      intro J hJ
      exact (masked_volume A S J (mem_powersetCard.mp hJ).2).symm

lemma retainedGram_erase {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) :
    retainedGram A (S.erase i) = retainedGram A S -
      Matrix.vecMulVec (fun p => A p i) (fun q => A q i) := by
  ext p q
  have h := sum_erase_add S (fun j => A p j * A q j) hi
  change (∑ j ∈ S.erase i, A p j * A q j) = (∑ j ∈ S, A p j * A q j) - A p i * A q i
  linarith

/-- Actual solve-based rejection score. -/
noncomputable def reverseDeletionScore {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  1 - (fun p => A p i) ⬝ᵥ ((retainedGram A S)⁻¹ *ᵥ (fun p => A p i))

lemma det_sub_vecMulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (v : Fin k → ℝ) (hM : M.det ≠ 0) :
    (M - Matrix.vecMulVec v v).det = M.det * (1 - v ⬝ᵥ (M⁻¹ *ᵥ v)) := by
  have h := Matrix.det_add_replicateCol_mul_replicateRow (ι := Fin 1)
    (A := M) (Ne.isUnit hM) (-v) v
  have hleft : M + Matrix.replicateCol (Fin 1) (-v) * Matrix.replicateRow (Fin 1) v =
      M - Matrix.vecMulVec v v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
    ring
  have hright : ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
      Matrix.replicateRow (Fin 1) v * M⁻¹ * Matrix.replicateCol (Fin 1) (-v)).det =
      1 - v ⬝ᵥ (M⁻¹ *ᵥ v) := by
    simp [← Matrix.replicateCol_mulVec, Matrix.mulVec_neg,
      ← Matrix.mulVec_mulVec, Matrix.replicateRow_mulVec_eq_const, sub_eq_add_neg]
  exact (congrArg Matrix.det hleft).symm.trans
    (h.trans (congrArg (fun x : ℝ => M.det * x) hright))

/-- The efficient solve score is exactly the retained-volume determinant ratio. -/
theorem reverse_score_eq_volume_ratio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n)) {i : Fin n}
    (hi : i ∈ S) (hV : retainedVolume A S ≠ 0) :
    reverseDeletionScore A S i = retainedVolume A (S.erase i) / retainedVolume A S := by
  have hM : (retainedGram A S).det ≠ 0 := by rwa [← retainedVolume_eq_det_gram]
  have heq : retainedVolume A (S.erase i) =
      retainedVolume A S * reverseDeletionScore A S i := by
    rw [retainedVolume_eq_det_gram, retainedGram_erase A S hi, det_sub_vecMulVec _ _ hM]
    rw [← retainedVolume_eq_det_gram]
    rfl
  rw [heq]
  field_simp [hV]

lemma reverse_score_bounds {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) (hV : 0 < retainedVolume A S) :
    0 ≤ reverseDeletionScore A S i ∧ reverseDeletionScore A S i ≤ 1 := by
  rw [reverse_score_eq_volume_ratio A S hi hV.ne']
  refine ⟨div_nonneg (retainedVolume_nonneg A _) hV.le, ?_⟩
  apply (div_le_one hV).mpr
  exact sum_le_sum_of_subset_of_nonneg (powersetCard_mono (erase_subset _ _))
    (fun J _ _ => volumeWeight_nonneg A J)

lemma retainedVolume_univ {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hA : OrthogonalRows A) : retainedVolume A univ = 1 :=
  volumeWeights_sum_eq_one A hA

lemma powersetCard_erase_filter {n k : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (S.erase i).powersetCard k = (S.powersetCard k).filter (fun J => i ∉ J) := by
  ext J
  simp only [mem_powersetCard, mem_filter, subset_erase]
  tauto

lemma sum_avoiding_subset {n : ℕ} (S J : Finset (Fin n)) (hJ : J ⊆ S) (w : ℝ) :
    ∑ i ∈ S, (if i ∉ J then w else 0) = ((S.card - J.card : ℕ) : ℝ) * w := by
  have hfilter : S.filter (fun i => i ∉ J) = S \ J := by ext i; simp
  rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul, card_sdiff_of_subset hJ]

/-- Every k-subset is counted once for each element of S outside that subset. -/
theorem reverse_deletion_mass {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, retainedVolume A (S.erase i) =
      ((S.card - k : ℕ) : ℝ) * retainedVolume A S := by
  simp only [retainedVolume, powersetCard_erase_filter, sum_filter]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro J hJ
  have hm := mem_powersetCard.mp hJ
  simpa only [hm.2] using sum_avoiding_subset S J hm.1 (volumeWeight A J)

/-- Normalized one-column deletion probability; zero at a zero-volume parent. -/
noncomputable def reverseDeleteProb {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  retainedVolume A (S.erase i) / (((S.card - k : ℕ) : ℝ) * retainedVolume A S)

lemma reverseDeleteProb_nonneg {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S : Finset (Fin n)) (i : Fin n) : 0 ≤ reverseDeleteProb A S i :=
  div_nonneg (retainedVolume_nonneg A _) (mul_nonneg (Nat.cast_nonneg _) (retainedVolume_nonneg A _))

theorem reverse_transition_normalization {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n))
    (hs : k < S.card) (hV : 0 < retainedVolume A S) :
    ∑ i ∈ S, reverseDeleteProb A S i = 1 := by
  simp only [reverseDeleteProb, ← sum_div, reverse_deletion_mass]
  exact div_self (mul_ne_zero (by exact_mod_cast (Nat.sub_pos_of_lt hs).ne') hV.ne')

/-- The literal finite r-step reverse deletion recursion. -/
noncomputable def reverseEndpointMass {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) :
    ℕ → Finset (Fin n) → Finset (Fin n) → ℝ
  | 0, S, J => if S = J then 1 else 0
  | r + 1, S, J => ∑ i ∈ S, reverseDeleteProb A S i * reverseEndpointMass A r (S.erase i) J

lemma volumeWeight_eq_zero_of_retained_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {S J : Finset (Fin n)}
    (hJ : J ∈ S.powersetCard k) (hV : retainedVolume A S = 0) :
    volumeWeight A J = 0 := by
  have hle : volumeWeight A J ≤ retainedVolume A S :=
    single_le_sum (fun T _ => volumeWeight_nonneg A T) hJ
  exact le_antisymm (hV ▸ hle) (volumeWeight_nonneg A J)

lemma reverse_endpoint_children_sum {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (S J : Finset (Fin n)) :
    ∑ i ∈ S, (if J ⊆ S.erase i ∧ J.card = k then volumeWeight A J else 0) =
      if J ⊆ S ∧ J.card = k then
        ((S.card - k : ℕ) : ℝ) * volumeWeight A J else 0 := by
  by_cases hJ : J ⊆ S ∧ J.card = k
  · simp only [subset_erase, hJ.1, hJ.2, true_and, and_true, ite_true]
    simpa only [hJ.2] using sum_avoiding_subset S J hJ.1 (volumeWeight A J)
  · have hz : ∀ i, ¬ (J ⊆ S.erase i ∧ J.card = k) := by
      intro i hi
      exact hJ ⟨hi.1.trans (erase_subset _ _), hi.2⟩
    simp [hJ, hz]

/-- Weighted endpoint law, valid even when a retained parent has zero volume. -/
theorem reverse_endpoint_weighted {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (r : ℕ) (S J : Finset (Fin n)) (hs : S.card = k + r) :
    retainedVolume A S * reverseEndpointMass A r S J =
      if J ⊆ S ∧ J.card = k then volumeWeight A J else 0 := by
  induction r generalizing S with
  | zero =>
    have hcard : S.card = k := by simpa using hs
    have hsets : S.powersetCard k = {S} := by
      ext T
      simp only [mem_powersetCard, mem_singleton]
      constructor
      · intro ht
        exact eq_of_subset_of_card_le ht.1 (by omega)
      · rintro rfl
        exact ⟨Subset.rfl, hcard⟩
    have hvol : retainedVolume A S = volumeWeight A S := by simp [retainedVolume, hsets]
    by_cases heq : S = J
    · subst J
      simp [reverseEndpointMass, hvol, hcard]
    · have hj : ¬ (J ⊆ S ∧ J.card = k) := by
        intro hc
        exact heq (eq_of_subset_of_card_le hc.1 (by omega)).symm
      simp [reverseEndpointMass, heq, hj]
  | succ r ih =>
    by_cases hV : retainedVolume A S = 0
    · rw [hV, zero_mul]
      split_ifs with hJ
      · exact (volumeWeight_eq_zero_of_retained_zero A (mem_powersetCard.mpr hJ) hV).symm
      · rfl
    · have hd : S.card - k = r + 1 := by omega
      have hdne : ((S.card - k : ℕ) : ℝ) ≠ 0 := by rw [hd]; positivity
      rw [reverseEndpointMass, mul_sum]
      have hterm : ∀ i ∈ S,
          retainedVolume A S *
            (reverseDeleteProb A S i * reverseEndpointMass A r (S.erase i) J) =
          (((S.card - k : ℕ) : ℝ))⁻¹ *
            (if J ⊆ S.erase i ∧ J.card = k then volumeWeight A J else 0) := by
        intro i hi
        have hc : (S.erase i).card = k + r := by rw [card_erase_of_mem hi]; omega
        have hiw := ih (S.erase i) hc
        calc _ = (((S.card - k : ℕ) : ℝ))⁻¹ *
            (retainedVolume A (S.erase i) * reverseEndpointMass A r (S.erase i) J) := by
              unfold reverseDeleteProb
              field_simp [hV, hdne]
          _ = _ := by rw [hiw]
      rw [sum_congr rfl hterm]
      rw [← mul_sum, reverse_endpoint_children_sum]
      split_ifs
      · field_simp [hdne]
      · simp

theorem reverse_sampler_law {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hA : OrthogonalRows A) (J : Finset (Fin n)) :
    reverseEndpointMass A (n - k) univ J = volumeWeight A J := by
  have hkn : k ≤ n := by
    by_contra hbad
    have hempty : (univ : Finset (Fin n)).powersetCard k = ∅ :=
      powersetCard_eq_empty.mpr (by simpa using Nat.lt_of_not_ge hbad)
    have hsum := volumeWeights_sum_eq_one A hA
    rw [hempty] at hsum
    simp at hsum
  have h := reverse_endpoint_weighted A (n-k) univ J (by simp; omega)
  rw [retainedVolume_univ A hA, one_mul] at h
  by_cases hJ : J.card = k
  · simpa [hJ] using h
  · simpa [hJ, volumeWeight] using h

/-- Explicit finite bound on the sum of ideal fast-stage geometric means.
This is an arithmetic sum bound, not an operational runtime theorem. -/
theorem reverse_fast_proposal_sum_le (k n : ℕ) :
    ∑ s ∈ Icc (2*k+1) n, (s : ℝ) / ((s-k : ℕ) : ℝ) ≤
      2 * ((n-2*k : ℕ) : ℝ) := by
  have hterm : ∀ s ∈ Icc (2*k+1) n,
      (s : ℝ) / ((s-k : ℕ) : ℝ) ≤ 2 := by
    intro s hs
    have hlow := (mem_Icc.mp hs).1
    have hpos : (0 : ℝ) < ((s-k : ℕ) : ℝ) := by exact_mod_cast (show 0 < s-k by omega)
    apply (div_le_iff₀ hpos).mpr
    exact_mod_cast (show s ≤ 2*(s-k) by omega)
  have hcard : (Icc (2*k+1) n).card = n-2*k := by
    rw [Nat.card_Icc]
    omega
  calc _ ≤ ∑ _s ∈ Icc (2*k+1) n, (2 : ℝ) := sum_le_sum hterm
    _ = _ := by simp [sum_const, nsmul_eq_mul, hcard, mul_comm]

end StructuredColumnSelection
