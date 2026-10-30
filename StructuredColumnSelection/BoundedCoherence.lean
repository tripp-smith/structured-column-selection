import StructuredColumnSelection.FrameCoherence
import StructuredColumnSelection.LeadingCoherence
import StructuredColumnSelection.StaticClass

/-!
# Bounded coherence does not restore a polynomial CPQR bound

For every `m ≥ 20`, the scaled triple-design frame has normalized coherence
at most `19/20`: filler pairs are at most the value of `(13/14 + ε)/(1 - ε)`
at `ε = 45/6400`, leading pairs are at most `1/2 + 1/m ≤ 11/20`, and mixed
pairs are at most the `m = 20` leading–filler ratio. The same frame beats
every `C (n + k + 1)^{2d}`.

Any cap `ρ ≥ 19/20` admits the same frames. A smaller cap is not ruled out.
This does not close outcome 1 or outcome 3, and it is not a polynomial bound
for every orthogonal-row matrix.
-/

namespace StructuredColumnSelection

open Classical Finset
open scoped Matrix

lemma filler_ratio_floor :
    (13 / 14 + 45 / 6400) / ((1 : ℝ) - 45 / 6400) = 83830 / 88970 := by
  norm_num

lemma filler_ratio_floor_lt : (83830 : ℝ) / 88970 < 19 / 20 := by
  norm_num

/-- The filler ratio increases in `ε` on `[0, 45/6400]`, and the value at the
right endpoint is strictly below `19/20`. -/
lemma filler_coeff_le {ε : ℝ} (hε : ε ≤ 45 / 6400) :
    (13 / 14 + ε) / (1 - ε) ≤ (19 : ℝ) / 20 := by
  have hden : 0 < 1 - ε := by
    have : (45 : ℝ) / 6400 < 1 := by norm_num
    linarith
  have hden0 : 0 < (1 : ℝ) - 45 / 6400 := by norm_num
  have hcross : (13 / 14 + ε) * (1 - 45 / 6400) ≤
      (13 / 14 + 45 / 6400) * (1 - ε) := by
    nlinarith [hε]
  have hmono : (13 / 14 + ε) / (1 - ε) ≤
      (13 / 14 + 45 / 6400) / (1 - 45 / 6400) :=
    (div_le_div_iff₀ hden hden0).2 hcross
  exact hmono.trans (le_of_lt (filler_ratio_floor.symm ▸ filler_ratio_floor_lt))

lemma half_plus_inv_le {m : ℕ} (hm : 20 ≤ m) :
    1 / 2 + 1 / (m : ℝ) ≤ 19 / 20 := by
  have hmR : (20 : ℝ) ≤ m := by exact_mod_cast hm
  have h1m : 1 / (m : ℝ) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) hmR
  calc (1 : ℝ) / 2 + 1 / (m : ℝ) ≤ 1 / 2 + 1 / 20 := by linarith
    _ = 11 / 20 := by norm_num
    _ ≤ 19 / 20 := by norm_num

lemma sqrt14_gt_thirtySeven_tenths : (37 : ℝ) / 10 < Real.sqrt 14 := by
  have h14 : ((37 : ℝ) / 10) ^ 2 < 14 := by norm_num
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 37 / 10)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) h14

lemma three_over_sqrt14_lt :
    3 * ((1 : ℝ) + 1 / 20) / Real.sqrt 14 < 63 / 74 := by
  have h1 : (1 : ℝ) + 1 / 20 = 21 / 20 := by norm_num
  rw [h1]
  have hrewrite : 3 * ((21 : ℝ) / 20) / Real.sqrt 14 = 63 / (20 * Real.sqrt 14) := by
    have hs : Real.sqrt 14 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [hs]
    norm_num
  rw [hrewrite]
  have hden : 0 < 20 * Real.sqrt 14 := by positivity
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 74)]
  have h74 : (74 : ℝ) < 20 * Real.sqrt 14 := by
    have : (74 : ℝ) = 20 * (37 / 10) := by norm_num
    rw [this]
    exact mul_lt_mul_of_pos_left sqrt14_gt_thirtySeven_tenths (by norm_num)
  nlinarith

lemma leading_in_m {m : ℝ} (hm : (20 : ℝ) ≤ m) :
    3 * (1 + 1 / m) / Real.sqrt 14 ≤ 3 * (1 + 1 / 20) / Real.sqrt 14 := by
  have h1m : 1 / m ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) hm
  have hsum : 1 + 1 / m ≤ 1 + 1 / 20 := by linarith
  have h3 : 0 ≤ (3 : ℝ) / Real.sqrt 14 := by positivity
  have hsne : Real.sqrt 14 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 14)).ne'
  have hL : 3 * (1 + 1 / m) / Real.sqrt 14 = (3 / Real.sqrt 14) * (1 + 1 / m) := by
    field_simp [hsne]
  have hR : 3 * (1 + 1 / 20) / Real.sqrt 14 =
      (3 / Real.sqrt 14) * (1 + 1 / 20) := by
    field_simp [hsne]
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hsum h3

lemma leading_filler_floor_sq :
    ((63 : ℝ) / 74 + 45 / 6400) ^ 2 < (19 / 20) ^ 2 * (1 - 45 / 6400) := by
  norm_num

lemma leading_filler_floor_lt :
    ((63 : ℝ) / 74 + 45 / 6400) / Real.sqrt (1 - 45 / 6400) < 19 / 20 := by
  have ha : 0 ≤ (63 : ℝ) / 74 + 45 / 6400 := by positivity
  have hbpos : 0 < (1 : ℝ) - 45 / 6400 := by norm_num
  have hsqrt := Real.sqrt_lt_sqrt (sq_nonneg _) leading_filler_floor_sq
  rw [Real.sqrt_sq ha] at hsqrt
  rw [Real.sqrt_mul (sq_nonneg ((19 : ℝ) / 20)),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19 / 20)] at hsqrt
  have hs : 0 < Real.sqrt ((1 : ℝ) - 45 / 6400) := Real.sqrt_pos.mpr hbpos
  rwa [div_lt_iff₀ hs]

/-- The leading–filler coefficient is increasing in `1/m` and in `ε`, so its
worst value on `m ≥ 20` and `ε ≤ 45/6400` is strictly below `19/20`. -/
lemma leading_filler_coeff_lt {m : ℕ} {ε : ℝ} (hm : 20 ≤ m) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 45 / 6400) :
    (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε) / Real.sqrt (1 - ε) < 19 / 20 := by
  have hmR : (20 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 ≤
      3 * (1 + 1 / 20) / Real.sqrt 14 := leading_in_m hmR
  have hnum : 3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε < 63 / 74 + 45 / 6400 := by
    linarith [three_over_sqrt14_lt, hα, hε]
  have hden : Real.sqrt (1 - 45 / 6400) ≤ Real.sqrt (1 - ε) := by
    apply Real.sqrt_le_sqrt
    linarith [hε]
  have hd0 : 0 < Real.sqrt (1 - 45 / 6400) := by
    apply Real.sqrt_pos.mpr
    norm_num
  have ha0 : 0 ≤ 3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε :=
    add_nonneg (by positivity) hε0
  have hle : (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε) / Real.sqrt (1 - ε) ≤
      (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε) / Real.sqrt (1 - 45 / 6400) :=
    div_le_div_of_nonneg_left ha0 hd0 hden
  have hlt : (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + ε) / Real.sqrt (1 - 45 / 6400) <
      (63 / 74 + 45 / 6400) / Real.sqrt (1 - 45 / 6400) :=
    div_lt_div_of_pos_right hnum hd0
  linarith [hle, hlt, leading_filler_floor_lt]

lemma tripleCount_sub_three {k : ℕ} (hk : 3 ≤ k) :
    tripleCount (k - 3) = 4 * ((k * (k - 1)) * (k - 2)) := by
  unfold tripleCount
  have h3 : k - 3 + 3 = k := Nat.sub_add_cancel hk
  have h2 : k - 3 + 2 = k - 1 := by omega
  have h1 : k - 3 + 1 = k - 2 := by omega
  rw [h3, h2, h1]

lemma design_block_le_repeats {k : ℕ} (hk : 1 ≤ k) :
    4 * ((k * (k - 1)) * (k - 2)) ≤ 32 * k ^ 4 := by
  have h1 : k - 1 ≤ k := Nat.sub_le _ _
  have h2 : k - 2 ≤ k := Nat.sub_le _ _
  have hprod : (k * (k - 1)) * (k - 2) ≤ k ^ 3 := by
    calc (k * (k - 1)) * (k - 2)
        ≤ (k * k) * (k - 2) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ ≤ (k * k) * k := Nat.mul_le_mul_left _ h2
      _ = k ^ 3 := by
          calc (k * k) * k = k * (k * k) := by ac_rfl
            _ = k * k ^ 2 := by rw [pow_two]
            _ = k ^ 3 := by rw [← pow_succ']
  have h4 : 4 * ((k * (k - 1)) * (k - 2)) ≤ 4 * k ^ 3 :=
    Nat.mul_le_mul_left 4 hprod
  have h8 : 1 ≤ 8 * k := by omega
  calc 4 * ((k * (k - 1)) * (k - 2))
      ≤ 4 * k ^ 3 := h4
    _ = 4 * k ^ 3 * 1 := by ring
    _ ≤ 4 * k ^ 3 * (8 * k) := Nat.mul_le_mul_left _ h8
    _ = 32 * k ^ 4 := by ring

lemma wideWidth_pow (m : ℕ) :
    wideWidth m = wideDim m + 32 * wideDim m ^ 4 := by
  unfold wideWidth wideRepeats
  have hmul : wideDim m * (32 * wideDim m ^ 3) = 32 * wideDim m ^ 4 := by
    calc wideDim m * (32 * wideDim m ^ 3)
        = 32 * (wideDim m * wideDim m ^ 3) := by ac_rfl
      _ = 32 * wideDim m ^ 4 := by rw [← pow_succ']
  rw [hmul]

/-- `n = k + 4 k (k - 1) (k - 2)` is at most `wideWidth m = k + 32 k ^ 4`. -/
lemma frame_columns_le_wide {m : ℕ} (hm : 20 ≤ m) :
    wideDim m + tripleCount (wideDim m - 3) + wideDim m + 1 ≤
      wideWidth m + wideDim m + 1 := by
  set k := wideDim m with hk
  have hk400 : 400 ≤ k := by
    rw [hk, wideDim]
    exact calc 400 = 20 * 20 := by norm_num
      _ ≤ m * m := Nat.mul_le_mul hm hm
  have hk3 : 3 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hN : tripleCount (k - 3) = 4 * ((k * (k - 1)) * (k - 2)) :=
    tripleCount_sub_three hk3
  have hw : wideWidth m = k + 32 * k ^ 4 := by
    simpa [hk] using wideWidth_pow m
  have hle : k + tripleCount (k - 3) + k + 1 ≤ wideWidth m + k + 1 := by
    calc k + tripleCount (k - 3) + k + 1
        = k + 4 * ((k * (k - 1)) * (k - 2)) + k + 1 := by rw [hN]
      _ = (k + k + 1) + 4 * ((k * (k - 1)) * (k - 2)) := by ring
      _ ≤ (k + k + 1) + 32 * k ^ 4 :=
          Nat.add_le_add_left (design_block_le_repeats hk1) _
      _ = (k + 32 * k ^ 4) + k + 1 := by ring
      _ = wideWidth m + k + 1 := by rw [hw]
  simpa [hk] using hle

lemma col_energy_eq_residualSq {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    vecEnergy (fun i => A i j) = residualSq A ∅ j := by
  rw [vecEnergy, residualSq_empty]

lemma mul_col_eq_mulVec {k N : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (a : Fin N) :
    (fun i => (C * W) i a) = C *ᵥ fun q => W q a := by
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- `ε = 45 / (16 k)` for the scaled block at dimension `wideDim m`. -/
noncomputable abbrev frameEps (m : ℕ) : ℝ := 45 / (16 * (wideDim m : ℝ))

/-- Filler width `tripleCount (k - 3)` at `k = wideDim m`. -/
abbrev fillerCount (m : ℕ) : ℕ := tripleCount (wideDim m - 3)

set_option maxHeartbeats 800000 in
/-- Normalized coherence at most `19/20` does not restore a polynomial CPQR
bound. The witness is the scaled triple-design frame at a large `m`. This
does not close outcome 3. It is not a polynomial bound for every
orthogonal-row matrix. A stricter coherence cap is not ruled out. -/
theorem bounded_coherence_no_polynomial (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (∀ j, 0 < residualSq A ∅ j) ∧
        (∀ j1 j2, j1 ≠ j2 →
          |colInner A j1 j2| ≤ (19 / 20) *
            (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2))) ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x := by
  have h9C : 0 < (9 : ℝ) * C := by positivity
  obtain ⟨m, hm, hpoly⟩ := exists_scale_beats_polynomial d h9C 20
  have hm20 : 20 ≤ m := (le_max_left (20 : ℕ) 2).trans hm
  have hm3 : 3 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  obtain ⟨A, Ccomp, W, x, hOrth, hLeft, hRight, _, _, hFrob, _, hSand, _, _,
      hWenergy, _, hSet, hImg, hGrow, hFF, hLF⟩ :=
    scaled_triple_frame_filler_coherence hm3
  have hk400 : 400 ≤ wideDim m := by
    rw [wideDim]
    exact calc 400 = 20 * 20 := by norm_num
      _ ≤ m * m := Nat.mul_le_mul hm20 hm20
  have hε0 : 0 ≤ frameEps m := by positivity
  have hε_le : frameEps m ≤ 45 / 6400 := by
    have hkR : (400 : ℝ) ≤ wideDim m := by exact_mod_cast hk400
    unfold frameEps
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hε1 : frameEps m < 1 := frame_eps_lt_one hm3
  have hone : 0 < 1 - frameEps m := by linarith [hε1]
  have hcmp : 1 - frameEps m ≤ 1 - frobEnergy (scaledBlock m) := by linarith [hFrob]
  have hratio_ff : (13 / 14 + frameEps m) / (1 - frameEps m) ≤ 19 / 20 :=
    filler_coeff_le hε_le
  have hratio_lf : (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + frameEps m) /
      Real.sqrt (1 - frameEps m) < 19 / 20 :=
    leading_filler_coeff_lt hm20 hε0 hε_le
  have hρll : 1 / 2 + 1 / (m : ℝ) ≤ 19 / 20 := half_plus_inv_le hm20
  have hsqrt_prod (j1 j2 : Fin (wideDim m + fillerCount m)) :
      0 ≤ Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hres (j : Fin (wideDim m + fillerCount m)) :
      vecEnergy (fun i => A i j) = residualSq A ∅ j :=
    col_energy_eq_residualSq A j
  have hpos : ∀ j : Fin (wideDim m + fillerCount m), 0 < residualSq A ∅ j := by
    intro j
    cases j using Fin.addCases with
    | left i =>
        rw [← hres]
        have hdiag : 0 < scaledBlock m i i := by
          rw [scaledBlock_diag]
          exact mul_pos (by norm_num) (wideDiag_pos hm2 i)
        have hsum : vecEnergy (fun row => A row (i.castAdd (fillerCount m))) =
            vecEnergy (fun row => scaledBlock m row i) := by
          unfold vecEnergy
          refine Finset.sum_congr rfl fun row _ => ?_
          show A row (i.castAdd (fillerCount m)) ^ 2 = scaledBlock m row i ^ 2
          rw [hLeft row i]
        rw [hsum]
        exact lt_of_lt_of_le (sq_pos_of_pos hdiag) (scaledBlock_col_energy_ge i)
    | right a =>
        rw [← hres]
        have hcol : (fun i => A i (a.natAdd (wideDim m))) =
            Ccomp *ᵥ fun q => W q a := by
          ext i
          rw [hRight i a]
          exact congrFun (mul_col_eq_mulVec Ccomp W a) i
        rw [hcol]
        have hWpos : 0 < vecEnergy (fun q => W q a) := by
          rw [hWenergy a]
          have hkR : (3 : ℝ) ≤ wideDim m := by
            exact_mod_cast (show 3 ≤ wideDim m by omega)
          have h1 : (0 : ℝ) < (wideDim m : ℝ) - 1 := by linarith
          have h2 : (0 : ℝ) < (wideDim m : ℝ) - 2 := by linarith
          exact div_pos (by norm_num) (by positivity)
        have hlow : (1 - frameEps m) * vecEnergy (fun q => W q a) ≤
            vecEnergy (Ccomp *ᵥ fun q => W q a) :=
          (mul_le_mul_of_nonneg_right hcmp (vecEnergy_nonneg _)).trans (hSand _).1
        exact lt_of_lt_of_le (mul_pos hone hWpos) hlow
  have hcoh : ∀ j1 j2 : Fin (wideDim m + fillerCount m), j1 ≠ j2 →
      |colInner A j1 j2| ≤ (19 / 20) *
        (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2)) := by
    intro j1 j2 hj
    have mixed (i : Fin (wideDim m)) (a : Fin (fillerCount m)) :
        |colInner A (i.castAdd (fillerCount m)) (a.natAdd (wideDim m))| ≤ (19 / 20) *
          (Real.sqrt (residualSq A ∅ (i.castAdd (fillerCount m))) *
            Real.sqrt (residualSq A ∅ (a.natAdd (wideDim m)))) := by
      have hinner : colInner A (i.castAdd (fillerCount m)) (a.natAdd (wideDim m)) =
          ∑ row, A row (i.castAdd (fillerCount m)) * A row (a.natAdd (wideDim m)) := rfl
      rw [hinner, ← hres, ← hres]
      exact (hLF i a).trans (mul_le_mul_of_nonneg_right (le_of_lt hratio_lf)
        (hsqrt_prod _ _))
    cases j1 using Fin.addCases with
    | left i1 =>
        cases j2 using Fin.addCases with
        | left i2 =>
            have hi : i1 ≠ i2 := by
              intro h
              apply hj
              simp [h]
            have hinner : colInner A (i1.castAdd (fillerCount m)) (i2.castAdd (fillerCount m)) =
                ∑ row, scaledBlock m row i1 * scaledBlock m row i2 := by
              unfold colInner
              refine Finset.sum_congr rfl fun row _ => ?_
              show A row (i1.castAdd (fillerCount m)) * A row (i2.castAdd (fillerCount m)) =
                scaledBlock m row i1 * scaledBlock m row i2
              rw [hLeft row i1, hLeft row i2]
            have hE1 : residualSq A ∅ (i1.castAdd (fillerCount m)) =
                vecEnergy (fun row => scaledBlock m row i1) := by
              rw [← hres]
              unfold vecEnergy
              refine Finset.sum_congr rfl fun row _ => ?_
              show A row (i1.castAdd (fillerCount m)) ^ 2 = scaledBlock m row i1 ^ 2
              rw [hLeft row i1]
            have hE2 : residualSq A ∅ (i2.castAdd (fillerCount m)) =
                vecEnergy (fun row => scaledBlock m row i2) := by
              rw [← hres]
              unfold vecEnergy
              refine Finset.sum_congr rfl fun row _ => ?_
              show A row (i2.castAdd (fillerCount m)) ^ 2 = scaledBlock m row i2 ^ 2
              rw [hLeft row i2]
            rw [hinner, hE1, hE2]
            exact (leading_leading_ratio hm2 hi).trans
              (mul_le_mul_of_nonneg_right hρll (mul_nonneg (Real.sqrt_nonneg _)
                (Real.sqrt_nonneg _)))
        | right a2 =>
            exact mixed i1 a2
    | right a1 =>
        cases j2 using Fin.addCases with
        | left i2 =>
            have hcomm : colInner A (a1.natAdd (wideDim m)) (i2.castAdd (fillerCount m)) =
                colInner A (i2.castAdd (fillerCount m)) (a1.natAdd (wideDim m)) := by
              unfold colInner
              refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
            rw [hcomm, mul_comm (Real.sqrt (residualSq A ∅ (a1.natAdd (wideDim m))))]
            exact mixed i2 a1
        | right a2 =>
            have ha : a1 ≠ a2 := by
              intro h
              apply hj
              simp [h]
            have hinner : colInner A (a1.natAdd (wideDim m)) (a2.natAdd (wideDim m)) =
                ∑ row, A row (a1.natAdd (wideDim m)) * A row (a2.natAdd (wideDim m)) := rfl
            rw [hinner, ← hres, ← hres]
            exact (hFF a1 a2 ha).trans
              (mul_le_mul_of_nonneg_right hratio_ff (hsqrt_prod _ _))
  have hsize : (wideDim m + fillerCount m) + wideDim m + 1 ≤ wideWidth m + wideDim m + 1 := by
    exact frame_columns_le_wide hm20
  have hpow : (((wideDim m + fillerCount m) + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) ≤
      ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsize) _
  have hNinth : C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) <
      wideGrowthLower m ^ 2 / 9 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 9)]
    have hcomm : C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) * 9 =
        ((9 : ℝ) * C) * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) := by
      ring
    rw [hcomm]
    exact hpoly
  refine ⟨wideDim m, wideDim m + fillerCount m, A, ?_⟩
  rw [hSet]
  refine ⟨x, hOrth, hpos, hcoh, ?_⟩
  calc
    C * (((wideDim m + fillerCount m) + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) *
        vecEnergy (selectedCols A
          (widePrefix (wideDim m + fillerCount m) (wideDim m)) *ᵥ x)
        = C * (((wideDim m + fillerCount m) + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) := by
          rw [hImg]
          ring
    _ ≤ C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hpow hC.le
    _ < wideGrowthLower m ^ 2 / 9 := hNinth
    _ ≤ vecEnergy x := hGrow

end StructuredColumnSelection
