import StructuredColumnSelection.DesignFrame
import StructuredColumnSelection.SymmetricCompletion
import StructuredColumnSelection.TripleDesign

/-!
# Scaled leading block and the triple-design frame

The design-frame pivot theorem of `DesignFrame.lean` needs filler energy
below `1 / wideRepeats m`, which the triple design does not meet. Scaling
the leading block by a constant `s` raises every leading residual to at
least `s² / (16 k²)`. Two facts make the scale affordable: the row
structure of `wideTriangular m` gives `‖R₀‖_F² ≤ 5 / (16 k)` (sharper than
the entrywise `1/4`), and the symmetric completion contracts,
`‖C w‖² ≤ ‖w‖²`, so filler energies are bounded by design column
energies with no factor `k`.

With `s = 3` and the triple design, every `m ≥ 3` gives an orthogonal-row
frame `[3 R₀ | C W]` whose CPQR set is the leading prefix and whose
inverse growth is at least `wideGrowthLower m ^ 2 / 9`.

No coherence bound on that frame is proved here. This does not close
outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset
open scoped Matrix

/-! ### Scaling identities -/

lemma frobEnergy_smul {k n : ℕ} (s : ℝ) (R : Matrix (Fin k) (Fin n) ℝ) :
    frobEnergy (s • R) = s ^ 2 * frobEnergy R := by
  unfold frobEnergy
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

lemma tailEnergy_smul {k : ℕ} (t : ℕ) (s : ℝ) (x : Fin k → ℝ) :
    tailEnergy t (s • x) = s ^ 2 * tailEnergy t x := by
  unfold tailEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma col_smul {k n : ℕ} (s : ℝ) (R : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    (s • R).col j = s • R.col j := by
  ext i
  simp [Matrix.col_apply]

/-! ### The sharp Frobenius bound for the triangular block -/

lemma wide_kc_sq_le {m : ℕ} (hm : 2 ≤ m) :
    (wideDim m : ℝ) * wideC m ^ 2 ≤ 1 / 4 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hden := wideDen_pos m
  unfold wideDim wideC
  push_cast
  rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (m : ℝ)]

lemma wideTriangular_offdiag_sq_le {m : ℕ} (hm : 2 ≤ m) {i j : Fin (wideDim m)}
    (hij : i ≠ j) : wideTriangular m i j ^ 2 ≤ wideC m ^ 2 * wideAlpha m ^ 2 := by
  have hd := wideDiag_pos hm i
  have hda := wideDiag_le_alpha hm i
  have hd2 : wideDiagNat m i ^ 2 ≤ wideAlpha m ^ 2 := by nlinarith
  unfold wideTriangular
  rw [if_neg hij]
  split_ifs
  · calc (-wideC m * wideDiagNat m i) ^ 2 = wideC m ^ 2 * wideDiagNat m i ^ 2 := by ring
      _ ≤ wideC m ^ 2 * wideAlpha m ^ 2 := mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
  · have : (0 : ℝ) ≤ wideC m ^ 2 * wideAlpha m ^ 2 := by positivity
    simpa using this

lemma wideTriangular_entry_sq_le' {m : ℕ} (hm : 2 ≤ m) (i j : Fin (wideDim m)) :
    wideTriangular m i j ^ 2 ≤
      wideC m ^ 2 * wideAlpha m ^ 2 + if i = j then wideAlpha m ^ 2 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, wideTriangular_diag]
    have hd := wideDiag_pos hm i
    have hda := wideDiag_le_alpha hm i
    have hd2 : wideDiagNat m i ^ 2 ≤ wideAlpha m ^ 2 := by nlinarith
    have : 0 ≤ wideC m ^ 2 * wideAlpha m ^ 2 := by positivity
    linarith
  · rw [if_neg hij, add_zero]
    exact wideTriangular_offdiag_sq_le hm hij

/-- Row structure gives `‖R₀‖_F² ≤ 5 / (16 k)`. -/
lemma wideTriangular_frob_le_sharp {m : ℕ} (hm : 2 ≤ m) :
    frobEnergy (wideTriangular m) ≤ 5 / (16 * (wideDim m : ℝ)) := by
  have hk := wideDim_pos hm
  have hkR : (0 : ℝ) < wideDim m := by exact_mod_cast hk
  have hrow : ∀ i : Fin (wideDim m), ∑ j, wideTriangular m i j ^ 2 ≤
      (wideDim m : ℝ) * (wideC m ^ 2 * wideAlpha m ^ 2) + wideAlpha m ^ 2 := by
    intro i
    calc ∑ j, wideTriangular m i j ^ 2
        ≤ ∑ j, (wideC m ^ 2 * wideAlpha m ^ 2 + if i = j then wideAlpha m ^ 2 else 0) :=
          Finset.sum_le_sum fun j _ => wideTriangular_entry_sq_le' hm i j
      _ = (wideDim m : ℝ) * (wideC m ^ 2 * wideAlpha m ^ 2) + wideAlpha m ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.sum_ite_eq]
          simp
  have hkc := wide_kc_sq_le hm
  have halpha : (wideDim m : ℝ) * wideAlpha m ^ 2 = 1 / (4 * (wideDim m : ℝ)) := by
    unfold wideAlpha
    field_simp
    ring
  calc frobEnergy (wideTriangular m)
      = ∑ i : Fin (wideDim m), ∑ j, wideTriangular m i j ^ 2 := rfl
    _ ≤ ∑ _i : Fin (wideDim m),
        ((wideDim m : ℝ) * (wideC m ^ 2 * wideAlpha m ^ 2) + wideAlpha m ^ 2) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = (wideDim m : ℝ) * ((wideDim m : ℝ) * (wideC m ^ 2 * wideAlpha m ^ 2) + wideAlpha m ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((wideDim m : ℝ) * wideC m ^ 2 + 1) * ((wideDim m : ℝ) * wideAlpha m ^ 2) := by ring
    _ ≤ (1 / 4 + 1) * (1 / (4 * (wideDim m : ℝ))) := by
        rw [halpha]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 5 / (16 * (wideDim m : ℝ)) := by
        field_simp
        ring

/-- The threshold `s² / (16 k²)` is below every scaled leading residual. -/
lemma wide_scaled_threshold_lt_diag {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0 < s)
    (p : Fin (wideDim m)) :
    s ^ 2 / (16 * (wideDim m : ℝ) ^ 2) < (s * wideDiagNat m p) ^ 2 := by
  have hk := wideDim_pos hm
  have hkR : (0 : ℝ) < wideDim m := by exact_mod_cast hk
  have hd := wideDiag_half_lower hm p.isLt
  have hhalf : 0 < wideAlpha m / 2 := by linarith [wideAlpha_pos hm]
  have hsq : (wideAlpha m / 2) ^ 2 < wideDiagNat m p ^ 2 :=
    sq_lt_sq.mpr (by
      rw [abs_of_pos hhalf, abs_of_pos (wideDiag_pos hm p)]
      exact hd)
  have halpha : (wideAlpha m / 2) ^ 2 = 1 / (16 * (wideDim m : ℝ) ^ 2) := by
    unfold wideAlpha
    field_simp
    ring
  have hs2 : 0 < s ^ 2 := by positivity
  calc s ^ 2 / (16 * (wideDim m : ℝ) ^ 2) = s ^ 2 * (wideAlpha m / 2) ^ 2 := by
        rw [halpha]; ring
    _ < s ^ 2 * wideDiagNat m p ^ 2 := mul_lt_mul_of_pos_left hsq hs2
    _ = (s * wideDiagNat m p) ^ 2 := by ring

/-! ### Scaled design-frame pivots -/

/-- With leading block `s R₀`, a contracting completion, and a tight design
whose columns have energy at most `s² / (16 k²)`, CPQR takes the leading
prefix. -/
theorem wide_scaled_design_pivots {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0 < s) {N : ℕ}
    (C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ)
    (hCC : (s • wideTriangular m) * (s • wideTriangular m)ᵀ + C * Cᵀ = 1)
    (hcontr : ∀ w : Fin (wideDim m) → ℝ, vecEnergy (C *ᵥ w) ≤ vecEnergy w)
    (W : Matrix (Fin (wideDim m)) (Fin N) ℝ) (hW : W * Wᵀ = 1)
    (hcol : ∀ j : Fin N, vecEnergy (fun q => W q j) ≤ s ^ 2 / (16 * (wideDim m : ℝ) ^ 2)) :
    OrthogonalRows (designFrame (s • wideTriangular m) C W) ∧
      cpqrSet (designFrame (s • wideTriangular m) C W) =
        widePrefix (wideDim m + N) (wideDim m) := by
  obtain ⟨hA, hR, _hF, _hE⟩ :=
    design_completion_orthogonal (s • wideTriangular m) C hCC W hW
  set A := designFrame (s • wideTriangular m) C W with hAdef
  have hkn : wideDim m ≤ wideDim m + N := Nat.le_add_right _ _
  have hcast (j : Fin (wideDim m)) : Fin.castLE hkn j = j.castAdd N := by rfl
  have hupper : ∀ i j : Fin (wideDim m), (j : ℕ) < (i : ℕ) →
      A i (Fin.castLE hkn j) = 0 := by
    intro i j h
    rw [hcast, hR, Matrix.smul_apply, wideTriangular_upper h, smul_zero]
  have hdiag : ∀ i : Fin (wideDim m), A i (Fin.castLE hkn i) ≠ 0 := by
    intro i
    rw [hcast, hR, Matrix.smul_apply, wideTriangular_diag, smul_eq_mul]
    exact mul_ne_zero hs.ne' (wideDiag_pos hm i).ne'
  have hfill : ∀ q : Fin N, vecEnergy (fun i => A i (q.natAdd (wideDim m))) ≤
      s ^ 2 / (16 * (wideDim m : ℝ) ^ 2) := by
    intro q
    rw [hAdef, designFrame_right_col]
    exact (hcontr _).trans (hcol q)
  have htail : ∀ p : Fin (wideDim m), ∀ j : Fin (wideDim m + N),
      (p : ℕ) < (j : ℕ) → tailEnergy p (A.col j) < A p (Fin.castLE hkn p) ^ 2 := by
    intro p j hpj
    rw [hcast, hR, Matrix.smul_apply, wideTriangular_diag, smul_eq_mul]
    by_cases hj : (j : ℕ) < wideDim m
    · let q : Fin (wideDim m) := ⟨j, hj⟩
      have hjq : j = q.castAdd N := by
        ext
        simp [q]
      have hpq : (p : ℕ) < (q : ℕ) := by
        have : (j : ℕ) = (q : ℕ) := by simp [hjq]
        omega
      have hcol' : A.col j = (s • wideTriangular m).col q := by
        ext i
        rw [hjq]
        exact hR i q
      rw [hcol', col_smul, tailEnergy_smul]
      have := wideTriangular_tail_lt hm p q hpq
      have hs2 : 0 < s ^ 2 := by positivity
      calc s ^ 2 * tailEnergy p ((wideTriangular m).col q)
          < s ^ 2 * wideDiagNat m p ^ 2 := mul_lt_mul_of_pos_left this hs2
        _ = (s * wideDiagNat m p) ^ 2 := by ring
    · have hge : wideDim m ≤ (j : ℕ) := Nat.le_of_not_lt hj
      let q : Fin N := ⟨(j : ℕ) - wideDim m, by
        have hjlt : (j : ℕ) < wideDim m + N := j.isLt
        omega⟩
      have hjq : j = q.natAdd (wideDim m) := by
        ext
        simp [q, Nat.add_sub_of_le hge]
      rw [hjq]
      exact (tailEnergy_le_energy p _).trans_lt
        ((hfill q).trans_lt (wide_scaled_threshold_lt_diag hm hs p))
  exact ⟨hA, triangular_prefix_pivots hkn A hupper hdiag htail (wideDim m) (Nat.le_refl _)⟩

/-- The scaled design frame with its inverse-growth witness. -/
theorem wide_scaled_design_adverse {m : ℕ} (hm : 2 ≤ m) {s : ℝ} (hs : 0 < s) {N : ℕ}
    (C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ)
    (hCC : (s • wideTriangular m) * (s • wideTriangular m)ᵀ + C * Cᵀ = 1)
    (hcontr : ∀ w : Fin (wideDim m) → ℝ, vecEnergy (C *ᵥ w) ≤ vecEnergy w)
    (W : Matrix (Fin (wideDim m)) (Fin N) ℝ) (hW : W * Wᵀ = 1)
    (hcol : ∀ j : Fin N, vecEnergy (fun q => W q j) ≤ s ^ 2 / (16 * (wideDim m : ℝ) ^ 2)) :
    ∃ x : Fin (widePrefix (wideDim m + N) (wideDim m)).card → ℝ,
      OrthogonalRows (designFrame (s • wideTriangular m) C W) ∧
      cpqrSet (designFrame (s • wideTriangular m) C W) =
        widePrefix (wideDim m + N) (wideDim m) ∧
      vecEnergy (selectedCols (designFrame (s • wideTriangular m) C W)
        (widePrefix (wideDim m + N) (wideDim m)) *ᵥ x) = 1 ∧
      wideGrowthLower m ^ 2 / s ^ 2 ≤ vecEnergy x := by
  obtain ⟨hA, hset⟩ := wide_scaled_design_pivots hm hs C hCC hcontr W hW hcol
  set A := designFrame (s • wideTriangular m) C W with hAdef
  have hR : ∀ i j : Fin (wideDim m), A i (j.castAdd N) = (s • wideTriangular m) i j :=
    designFrame_left (s • wideTriangular m) C W
  have hkn : wideDim m ≤ wideDim m + N := Nat.le_add_right _ _
  let J := widePrefix (wideDim m + N) (wideDim m)
  let hcard : J.card = wideDim m := widePrefix_card hkn
  let y : Fin (wideDim m) → ℝ := wideWitness m
  let x : Fin J.card → ℝ := fun j => y (Fin.cast hcard j) / s
  have hcast : ∀ j : Fin (wideDim m), Fin.castLE hkn j = j.castAdd N := fun _ => rfl
  have hmul : selectedCols A J *ᵥ x = wideTriangular m *ᵥ y := by
    ext i
    simp only [Matrix.mulVec, dotProduct_eq]
    refine Fintype.sum_equiv (finCongr hcard)
      (fun j => selectedCols A J i j * x j)
      (fun j => wideTriangular m i j * y j) ?_
    intro j
    rw [selectedCols_widePrefix_apply hkn]
    rw [hcast (Fin.cast hcard j), hR, Matrix.smul_apply, smul_eq_mul]
    simp only [x, y, finCongr_apply]
    field_simp
  refine ⟨x, hA, hset, ?_, ?_⟩
  · rw [hmul]
    exact wideWitness_image_energy hm
  · have hx : vecEnergy x = vecEnergy y / s ^ 2 := by
      unfold vecEnergy
      rw [Finset.sum_div]
      refine Fintype.sum_equiv (finCongr hcard) _ _ ?_
      intro j
      simp only [x, y, finCongr_apply]
      ring
    rw [hx]
    have hs2 : 0 < s ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (wideWitness_energy_lower hm) hs2.le

/-! ### Row reindexing of a design -/

lemma design_reindex {k k' N : ℕ} (e : Fin k ≃ Fin k') (W : Matrix (Fin k') (Fin N) ℝ)
    (hW : W * Wᵀ = 1) :
    W.submatrix e id * (W.submatrix e id)ᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W.submatrix e id i j) = vecEnergy (fun i => W i j)) ∧
      ∀ a b, ∑ i, W.submatrix e id i a * W.submatrix e id i b = ∑ i, W i a * W i b := by
  refine ⟨?_, ?_, ?_⟩
  · ext i i'
    have h := congrFun (congrFun hW (e i)) (e i')
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id] at h ⊢
    rw [h, Matrix.one_apply, Matrix.one_apply]
    simp only [e.injective.eq_iff]
  · intro j
    unfold vecEnergy
    exact Equiv.sum_comp e (fun i => W i j ^ 2)
  · intro a b
    exact Equiv.sum_comp e (fun i => W i a * W i b)

/-! ### The instantiation with the triple design -/

/-- The leading block `3 R₀`. -/
noncomputable def scaledBlock (m : ℕ) : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ :=
  (3 : ℝ) • wideTriangular m

lemma scaledBlock_frob_le {m : ℕ} (hm : 2 ≤ m) :
    frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) := by
  unfold scaledBlock
  rw [frobEnergy_smul]
  have h := wideTriangular_frob_le_sharp hm
  have hk := wideDim_pos hm
  have hkR : (0 : ℝ) < wideDim m := by exact_mod_cast hk
  calc (3 : ℝ) ^ 2 * frobEnergy (wideTriangular m) ≤ 3 ^ 2 * (5 / (16 * (wideDim m : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 45 / (16 * (wideDim m : ℝ)) := by ring

lemma wideDim_ge_nine {m : ℕ} (hm : 3 ≤ m) : 9 ≤ wideDim m := by
  unfold wideDim
  have := Nat.mul_le_mul hm hm
  omega

lemma scaledBlock_frob_le_one {m : ℕ} (hm : 3 ≤ m) : frobEnergy (scaledBlock m) ≤ 1 := by
  have h := scaledBlock_frob_le (by omega : 2 ≤ m)
  have hk := wideDim_ge_nine hm
  have hkR : (9 : ℝ) ≤ wideDim m := by exact_mod_cast hk
  calc frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) := h
    _ ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith

/-- The triple design column energy `1 / (4 (k-1)(k-2))` is below the scaled
threshold `9 / (16 k²)` once `k ≥ 5`. -/
lemma triple_energy_le_threshold {k : ℝ} (hk : 5 ≤ k) :
    1 / (4 * ((k - 1) * (k - 2))) ≤ 3 ^ 2 / (16 * k ^ 2) := by
  have h1 : 0 < (k - 1) * (k - 2) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- For every `m ≥ 3`, the frame `[3 R₀ | C W]` with the symmetric completion
`C` and the triple design `W` has orthogonal rows, CPQR set equal to the
leading prefix, and inverse growth at least `wideGrowthLower m ^ 2 / 9`. The
statement also records the completion identities of `C` and the design
properties of `W`. -/
theorem scaled_triple_frame {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + tripleCount (wideDim m - 3))) ℝ,
    ∃ C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ,
    ∃ W : Matrix (Fin (wideDim m)) (Fin (tripleCount (wideDim m - 3))) ℝ,
    ∃ x : Fin (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)).card → ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin (wideDim m), A i (j.castAdd _) = scaledBlock m i j) ∧
      (∀ (i : Fin (wideDim m)) (j : Fin (tripleCount (wideDim m - 3))),
        A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
      Cᵀ = C ∧ scaledBlock m * (scaledBlock m)ᵀ + C * Cᵀ = 1 ∧
      frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) ∧
      (∀ w v : Fin (wideDim m) → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - ((scaledBlock m)ᵀ *ᵥ w) ⬝ᵥ ((scaledBlock m)ᵀ *ᵥ v)) ∧
      (∀ w : Fin (wideDim m) → ℝ,
        (1 - frobEnergy (scaledBlock m)) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      (∀ v : Fin (wideDim m) → ℝ,
        vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy (scaledBlock m) ^ 2 * vecEnergy v) ∧
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) =
        1 / (4 * (((wideDim m : ℝ) - 1) * ((wideDim m : ℝ) - 2)))) ∧
      (∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
        13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
          Real.sqrt (vecEnergy (fun i => W i b)))) ∧
      cpqrSet A = widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m) ∧
      vecEnergy (selectedCols A
        (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)) *ᵥ x) = 1 ∧
      wideGrowthLower m ^ 2 / 9 ≤ vecEnergy x := by
  have hm2 : 2 ≤ m := by omega
  have hk9 := wideDim_ge_nine hm
  set k := wideDim m with hkdef
  set n := k - 3 with hndef
  have hkn : k = n + 3 := by omega
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk9
  have hnR : (n : ℝ) = (k : ℝ) - 3 := by
    rw [hndef, Nat.cast_sub (by omega : 3 ≤ k)]
    norm_num
  -- The reindexed triple design.
  let e : Fin k ≃ Fin (n + 3) := finCongr hkn
  let W : Matrix (Fin k) (Fin (tripleCount n)) ℝ := (tripleDesignFin n).submatrix e id
  obtain ⟨hWW, hWE, hWI⟩ := design_reindex e (tripleDesignFin n) (tripleDesignFin_gram n)
  have hWenergy : ∀ j, vecEnergy (fun i => W i j) =
      1 / (4 * (((k : ℝ) - 1) * ((k : ℝ) - 2))) := by
    intro j
    show vecEnergy (fun i => (tripleDesignFin n).submatrix e id i j) = _
    rw [hWE j, tripleDesignFin_col_energy, hnR]
    ring_nf
  have hWcoh : ∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
        Real.sqrt (vecEnergy (fun i => W i b))) := by
    intro a b hab
    show |∑ i, (tripleDesignFin n).submatrix e id i a * (tripleDesignFin n).submatrix e id i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => (tripleDesignFin n).submatrix e id i a)) *
        Real.sqrt (vecEnergy (fun i => (tripleDesignFin n).submatrix e id i b)))
    rw [hWI a b, hWE a, hWE b]
    exact tripleDesignFin_coherence n hab
  have hcol : ∀ j, vecEnergy (fun q => W q j) ≤ (3 : ℝ) ^ 2 / (16 * (k : ℝ) ^ 2) := by
    intro j
    rw [hWenergy j]
    exact triple_energy_le_threshold (by linarith)
  -- The symmetric completion.
  have hfrob1 := scaledBlock_frob_le_one hm
  obtain ⟨C, hsym, hCC, hinner, hsand, hpert⟩ := symmetric_completion (scaledBlock m) hfrob1
  have hcontr : ∀ w : Fin k → ℝ, vecEnergy (C *ᵥ w) ≤ vecEnergy w := fun w => (hsand w).2
  have hCC' : ((3 : ℝ) • wideTriangular m) * ((3 : ℝ) • wideTriangular m)ᵀ + C * Cᵀ = 1 := hCC
  obtain ⟨x, hA, hset, himg, hgrow⟩ :=
    wide_scaled_design_adverse hm2 (by norm_num : (0 : ℝ) < 3) C hCC' hcontr W hWW hcol
  refine ⟨designFrame (scaledBlock m) C W, C, W, x, hA, designFrame_left _ _ _,
    designFrame_right _ _ _, hsym, hCC, scaledBlock_frob_le hm2, hinner, hsand, hpert, hWW,
    hWenergy, hWcoh, hset, himg, ?_⟩
  calc wideGrowthLower m ^ 2 / 9 = wideGrowthLower m ^ 2 / (3 : ℝ) ^ 2 := by norm_num
    _ ≤ vecEnergy x := hgrow

end StructuredColumnSelection
