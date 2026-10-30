import StructuredColumnSelection.WideCPQRFamily
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort

/-! Inverse-energy witness for the wide triangular family, and the quantifier
that turns its geometric growth into a failure of every joint polynomial. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

/-- Proposed inverse-norm scale `(2m/3)·(4/3)^(m-1)`. -/
noncomputable def wideGrowthLower (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / 3) * ((4 : ℝ) / 3) ^ (m - 1)

lemma wideGrowthLower_nonneg {m : ℕ} (hm : 1 ≤ m) : 0 ≤ wideGrowthLower m := by
  unfold wideGrowthLower
  positivity

lemma wideDim_sq (m : ℕ) : (wideDim m : ℝ) = (m : ℝ) ^ 2 := by
  unfold wideDim
  push_cast
  ring

lemma wide_two_le_dim {m : ℕ} (hm : 2 ≤ m) : 2 ≤ wideDim m := by
  unfold wideDim
  nlinarith

/-- Back-substitution witness for `R x = e_{last}`. -/
noncomputable def wideWitness (m : ℕ) (i : Fin (wideDim m)) : ℝ :=
  if (i : ℕ) + 1 = wideDim m then
    1 / wideDiagNat m (wideDim m - 1)
  else
    wideC m * (1 + wideC m) ^ (wideDim m - 2 - (i : ℕ)) /
      wideDiagNat m (wideDim m - 1)

lemma wideWitness_head {m : ℕ} (hm : 2 ≤ m) :
    wideWitness m ⟨0, wideDim_pos hm⟩ =
      wideC m * (1 + wideC m) ^ (wideDim m - 2) /
        wideDiagNat m (wideDim m - 1) := by
  have hk := wide_two_le_dim hm
  have hne : ¬ ((0 : ℕ) + 1 = wideDim m) := by omega
  simp [wideWitness, hne]

lemma wide_diag_last (m : ℕ) :
    wideDiagNat m (wideDim m - 1) =
      wideAlpha m * wideEps m ^ (wideDim m - 1) := rfl

lemma wide_head_factor {m : ℕ} (hm : 2 ≤ m) :
    wideC m * (1 + wideC m) ^ (wideDim m - 2) /
        (wideAlpha m * wideEps m ^ (wideDim m - 1)) =
      (4 * (m : ℝ) * (wideDim m : ℝ) / (4 * (wideDim m : ℝ) - 1)) *
        ((4 * (wideDim m : ℝ) + 2 * (m : ℝ) + 1) /
          (4 * (wideDim m : ℝ) - 1)) ^ (wideDim m - 2) := by
  have hk := wide_two_le_dim hm
  set M : ℝ := (m : ℝ)
  set K : ℝ := (wideDim m : ℝ)
  set D : ℝ := 4 * M ^ 2 + 1
  set E : ℝ := 4 * K - 1
  set N : ℝ := 4 * K + 2 * M + 1
  have hK : K = M ^ 2 := wideDim_sq m
  have hDpos : (0 : ℝ) < D := by
    dsimp [D]; positivity
  have hEpos : (0 : ℝ) < E := by
    dsimp [E]; rw [hK]
    have hM : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have : (2 : ℝ) ≤ M := by simpa [M] using hM
    nlinarith
  have hDne : D ≠ 0 := hDpos.ne'
  have hEne : E ≠ 0 := hEpos.ne'
  have hc : wideC m = 2 * M / D := by
    unfold wideC
    simp [M, D]
  have hα : wideAlpha m = 1 / (2 * K) := by
    unfold wideAlpha
    simp [K]
  have hε : wideEps m = E / D := by
    unfold wideEps
    simp [E, D, hK, M]
  have h1c : 1 + 2 * M / D = N / D := by
    field_simp [hDne]
    dsimp [N, D]
    rw [hK]
    ring
  have hDpow : D ^ (wideDim m - 1) = D * D ^ (wideDim m - 2) := by
    have hstep : wideDim m - 1 = (wideDim m - 2) + 1 := by omega
    rw [hstep, pow_succ']
  have hA : wideC m * (1 + wideC m) ^ (wideDim m - 2) =
      2 * M * N ^ (wideDim m - 2) / D ^ (wideDim m - 1) := by
    rw [hc, h1c, div_pow, hDpow]
    field_simp [hDne]
  have hB : (wideAlpha m * wideEps m ^ (wideDim m - 1))⁻¹ =
      2 * K * D ^ (wideDim m - 1) / E ^ (wideDim m - 1) := by
    rw [hα, hε, div_pow]
    field_simp [hDne, hEne]
  have hR : (4 * M * K / E) * (N / E) ^ (wideDim m - 2) =
      4 * M * K * N ^ (wideDim m - 2) / E ^ (wideDim m - 1) := by
    rw [div_pow]
    have hstep : E ^ (wideDim m - 1) = E * E ^ (wideDim m - 2) := by
      have hsub : wideDim m - 1 = (wideDim m - 2) + 1 := by omega
      rw [hsub, pow_succ']
    rw [hstep]
    field_simp [hEne]
  calc
    wideC m * (1 + wideC m) ^ (wideDim m - 2) /
        (wideAlpha m * wideEps m ^ (wideDim m - 1))
      = (2 * M * N ^ (wideDim m - 2) / D ^ (wideDim m - 1)) *
          (2 * K * D ^ (wideDim m - 1) / E ^ (wideDim m - 1)) := by
            rw [div_eq_mul_inv, hA, hB]
    _ = 4 * M * K * N ^ (wideDim m - 2) / E ^ (wideDim m - 1) := by
          field_simp [hDne]
          ring
    _ = (4 * M * K / E) * (N / E) ^ (wideDim m - 2) := hR.symm
    _ = _ := by
          simp [M, K, E, N]

lemma wide_prefactor_ge {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) ≤ 4 * (m : ℝ) * (wideDim m : ℝ) / (4 * (wideDim m : ℝ) - 1) := by
  have hM : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hE : (0 : ℝ) < 4 * (wideDim m : ℝ) - 1 := by
    rw [wideDim_sq]
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  rw [le_div_iff₀ hE]
  rw [wideDim_sq]
  nlinarith

lemma wide_ratio_ge {m : ℕ} (hm : 2 ≤ m) :
    (2 * (m : ℝ) + 1) / (2 * (m : ℝ)) ≤
      (4 * (wideDim m : ℝ) + 2 * (m : ℝ) + 1) / (4 * (wideDim m : ℝ) - 1) := by
  have hM : (0 : ℝ) < 2 * (m : ℝ) := by
    exact_mod_cast (show 0 < 2 * m by omega)
  have hE : (0 : ℝ) < 4 * (wideDim m : ℝ) - 1 := by
    rw [wideDim_sq]
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  rw [div_le_div_iff₀ hM hE, wideDim_sq]
  nlinarith

lemma wide_simple_pow_ge {m : ℕ} (hm : 2 ≤ m) :
    (3 : ℝ) / 2 ≤ ((2 * (m : ℝ) + 1) / (2 * (m : ℝ))) ^ m := by
  have hM : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hber := one_add_mul_le_pow (a := 1 / (2 * (m : ℝ)))
    (by
      have : (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) := by positivity
      linarith) m
  have hsum : (1 : ℝ) + (m : ℝ) * (1 / (2 * (m : ℝ))) = 3 / 2 := by
    field_simp [hM]
    ring
  have hbase : (1 : ℝ) + 1 / (2 * (m : ℝ)) = (2 * (m : ℝ) + 1) / (2 * (m : ℝ)) := by
    field_simp [hM]
  rw [hsum, hbase] at hber
  exact hber

lemma wide_exponent_le {m : ℕ} (hm : 2 ≤ m) :
    m * (m - 1) ≤ wideDim m - 2 := by
  unfold wideDim
  have hmul : 2 ≤ m * m := by
    have h4 : 2 * 2 ≤ m * m := Nat.mul_le_mul hm hm
    omega
  rw [Nat.le_sub_iff_add_le hmul]
  have hcancel : m * (m - 1) + m = m * m := by
    have hm1 : 1 ≤ m := by omega
    calc
      m * (m - 1) + m = m * ((m - 1) + 1) := by rw [Nat.mul_succ]
      _ = m * m := by rw [Nat.sub_add_cancel hm1]
  omega

lemma wideWitness_head_lower {m : ℕ} (hm : 2 ≤ m) :
    wideGrowthLower m ≤ wideWitness m ⟨0, wideDim_pos hm⟩ := by
  rw [wideWitness_head hm, wide_diag_last]
  rw [wide_head_factor hm]
  set M : ℝ := (m : ℝ)
  set K : ℝ := (wideDim m : ℝ)
  set simple : ℝ := (2 * M + 1) / (2 * M)
  set base : ℝ := (4 * K + 2 * M + 1) / (4 * K - 1)
  set pre : ℝ := 4 * M * K / (4 * K - 1)
  have hpre : M ≤ pre := by
    simpa [pre, M, K] using wide_prefactor_ge hm
  have hbase : simple ≤ base := by
    simpa [simple, base, M, K] using wide_ratio_ge hm
  have hsimple0 : 0 ≤ simple := by
    dsimp [simple, M]; positivity
  have hbase0 : 0 ≤ base := hsimple0.trans hbase
  have hpow1 : simple ^ (wideDim m - 2) ≤ base ^ (wideDim m - 2) :=
    pow_le_pow_left₀ hsimple0 hbase _
  have hexp : m * (m - 1) ≤ wideDim m - 2 := wide_exponent_le hm
  have hsimple1 : 1 ≤ simple := by
    dsimp [simple, M]
    have hM : (0 : ℝ) < 2 * M := by positivity
    rw [le_div_iff₀ hM]
    linarith
  have hpow2 : simple ^ (m * (m - 1)) ≤ simple ^ (wideDim m - 2) :=
    pow_le_pow_right₀ hsimple1 hexp
  have hgroup : simple ^ (m * (m - 1)) = (simple ^ m) ^ (m - 1) := by
    rw [pow_mul]
  have h32 : (3 : ℝ) / 2 ≤ simple ^ m := by
    simpa [simple, M] using wide_simple_pow_ge hm
  have hpow4 : ((3 : ℝ) / 2) ^ (m - 1) ≤ (simple ^ m) ^ (m - 1) :=
    pow_le_pow_left₀ (by norm_num) h32 _
  have h43 : ((4 : ℝ) / 3) ≤ (3 : ℝ) / 2 := by norm_num
  have hpow5 : ((4 : ℝ) / 3) ^ (m - 1) ≤ ((3 : ℝ) / 2) ^ (m - 1) :=
    pow_le_pow_left₀ (by norm_num) h43 _
  have hMle : 2 * M / 3 ≤ M := by
    dsimp [M]
    have : (0 : ℝ) ≤ M := by positivity
    linarith
  have hchain : (2 * M / 3) * ((4 : ℝ) / 3) ^ (m - 1) ≤ pre * base ^ (wideDim m - 2) := by
    calc
      (2 * M / 3) * ((4 : ℝ) / 3) ^ (m - 1)
          ≤ M * ((4 : ℝ) / 3) ^ (m - 1) :=
            mul_le_mul_of_nonneg_right hMle (by positivity)
      _ ≤ M * ((3 : ℝ) / 2) ^ (m - 1) :=
            mul_le_mul_of_nonneg_left hpow5 (by positivity)
      _ ≤ M * (simple ^ m) ^ (m - 1) :=
            mul_le_mul_of_nonneg_left hpow4 (by positivity)
      _ = M * simple ^ (m * (m - 1)) := by rw [hgroup]
      _ ≤ M * simple ^ (wideDim m - 2) :=
            mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ ≤ M * base ^ (wideDim m - 2) :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ ≤ pre * base ^ (wideDim m - 2) :=
            mul_le_mul_of_nonneg_right hpre (pow_nonneg hbase0 _)
  simpa [wideGrowthLower, pre, base, M] using hchain

lemma sum_gt_split {k : ℕ} {r : ℕ} (hr : r + 1 < k) (f : Fin k → ℝ) :
    (∑ j : Fin k, if r < (j : ℕ) then f j else 0) =
      f ⟨r + 1, hr⟩ +
        (∑ j : Fin k, if r + 1 < (j : ℕ) then f j else 0) := by
  let idx : Fin k := ⟨r + 1, hr⟩
  rw [← add_sum_erase univ (fun j : Fin k => if r < (j : ℕ) then f j else 0) (mem_univ idx)]
  have hhead : (if r < (idx : ℕ) then f idx else 0) = f idx := by
    simp [idx]
  rw [hhead]
  have hfun : (∑ j ∈ univ.erase idx, if r < (j : ℕ) then f j else 0) =
      ∑ j ∈ univ.erase idx, if r + 1 < (j : ℕ) then f j else 0 := by
    refine sum_congr rfl ?_
    intro j hj
    have hne : j ≠ idx := (mem_erase.mp hj).1
    by_cases hgt : r + 1 < (j : ℕ)
    · simp [hgt, show r < (j : ℕ) by omega]
    · by_cases hrj : r < (j : ℕ)
      · have hval : (j : ℕ) = r + 1 := by omega
        exact (hne (Fin.ext hval)).elim
      · simp [hgt, hrj]
  rw [hfun]
  congr 1
  exact Finset.sum_erase (univ : Finset (Fin k))
    (f := fun j : Fin k => if r + 1 < (j : ℕ) then f j else 0)
    (a := idx) (by simp [idx])

lemma wideWitness_suffix {m : ℕ} (hm : 2 ≤ m) (t : ℕ) (ht : t < wideDim m) :
    (∑ j : Fin (wideDim m),
        if wideDim m - 1 - t < (j : ℕ) then wideWitness m j else 0) =
      if t = 0 then 0
      else (1 + wideC m) ^ (t - 1) / wideDiagNat m (wideDim m - 1) := by
  have hk := wide_two_le_dim hm
  induction t with
  | zero =>
    simp only [if_true, Nat.sub_zero]
    apply Finset.sum_eq_zero
    intro j _
    have hnot : ¬ wideDim m - 1 < (j : ℕ) := by
      have := j.isLt
      omega
    simp [hnot]
  | succ t ih =>
    have ht0 : t < wideDim m := Nat.lt_of_succ_lt ht
    have ih' := ih ht0
    have hr : wideDim m - 2 - t + 1 < wideDim m := by omega
    have htailNat : wideDim m - 1 - (t + 1) = wideDim m - 2 - t := by omega
    have hnextNat : wideDim m - 2 - t + 1 = wideDim m - 1 - t := by omega
    have hsplit := sum_gt_split (k := wideDim m) (r := wideDim m - 2 - t) hr
      (wideWitness m)
    have hsumEq :
        (∑ j : Fin (wideDim m), if wideDim m - 1 - (t + 1) < (j : ℕ) then
          wideWitness m j else 0) =
        (∑ j : Fin (wideDim m), if wideDim m - 2 - t < (j : ℕ) then
          wideWitness m j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [htailNat]
    rw [hsumEq, hsplit]
    have hheadFin : (⟨wideDim m - 2 - t + 1, hr⟩ : Fin (wideDim m)) =
        ⟨wideDim m - 1 - t, by omega⟩ := Fin.ext (by omega)
    rw [hheadFin]
    have hsumNext :
        (∑ j : Fin (wideDim m), if wideDim m - 2 - t + 1 < (j : ℕ) then
          wideWitness m j else 0) =
        (∑ j : Fin (wideDim m), if wideDim m - 1 - t < (j : ℕ) then
          wideWitness m j else 0) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      simp [hnextNat]
    rw [hsumNext]
    have hsucc0 : ¬ t + 1 = 0 := by omega
    simp only [hsucc0, if_false]
    have hexpSucc : t + 1 - 1 = t := by omega
    rw [hexpSucc]
    by_cases htzero : t = 0
    · subst htzero
      simp only [ih', if_true, add_zero]
      have hval : ((⟨wideDim m - 1, by omega⟩ : Fin (wideDim m)) : ℕ) =
          wideDim m - 1 := rfl
      have hidx' : ((⟨wideDim m - 1, by omega⟩ : Fin (wideDim m)) : ℕ) + 1 =
          wideDim m := by
        rw [hval]
        omega
      simp [wideWitness, hidx', pow_zero]
    · simp only [htzero, if_false] at ih'
      rw [ih']
      set idx : Fin (wideDim m) := ⟨wideDim m - 1 - t, by omega⟩
      have hval : (idx : ℕ) = wideDim m - 1 - t := rfl
      have hnot : ¬ (idx : ℕ) + 1 = wideDim m := by
        rw [hval]
        omega
      have hexp : wideDim m - 2 - (idx : ℕ) = t - 1 := by
        rw [hval]
        omega
      simp only [wideWitness, hnot, if_false, hexp]
      have hd : wideDiagNat m (wideDim m - 1) ≠ 0 := (wideDiag_pos hm _).ne'
      field_simp [hd]
      conv_rhs =>
        rw [show t = (t - 1) + 1 by omega]
        rw [pow_succ]
      ring

lemma wideTriangular_mulVec_apply {m : ℕ} (x : Fin (wideDim m) → ℝ)
    (i : Fin (wideDim m)) :
    (wideTriangular m *ᵥ x) i =
      wideDiagNat m i * (x i - wideC m *
        ∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then x j else 0) := by
  rw [Matrix.mulVec, dotProduct_eq]
  have hsplit := add_sum_erase (univ : Finset (Fin (wideDim m)))
    (fun j => wideTriangular m i j * x j) (mem_univ i)
  rw [← hsplit]
  have hdiag : wideTriangular m i i * x i = wideDiagNat m i * x i := by
    rw [wideTriangular_diag]
  rw [hdiag]
  have hoff : (∑ j ∈ univ.erase i, wideTriangular m i j * x j) =
      ∑ j ∈ univ.erase i, if (i : ℕ) < (j : ℕ) then
        -wideC m * wideDiagNat m i * x j else 0 := by
    refine sum_congr rfl fun j hj => ?_
    have hne : j ≠ i := (mem_erase.mp hj).1
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · have hne' : i ≠ j := Ne.symm hne
      simp [wideTriangular, hne', hlt]
    · have hgt : (j : ℕ) < (i : ℕ) := by
        have hval : (j : ℕ) ≠ (i : ℕ) := fun h => hne (Fin.ext h)
        omega
      rw [wideTriangular_upper hgt]
      simp [hlt]
  rw [hoff]
  have hzero : (if (i : ℕ) < (i : ℕ) then
      -wideC m * wideDiagNat m i * x i else 0) = 0 := by simp
  have herase : (∑ j ∈ univ.erase i, if (i : ℕ) < (j : ℕ) then
      -wideC m * wideDiagNat m i * x j else 0) =
      ∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then
        -wideC m * wideDiagNat m i * x j else 0 := by
    exact Finset.sum_erase (univ : Finset (Fin (wideDim m)))
      (a := i)
      (f := fun j : Fin (wideDim m) => if (i : ℕ) < (j : ℕ) then
        -wideC m * wideDiagNat m i * x j else 0) hzero
  rw [herase]
  have hfactor : (∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then
      -wideC m * wideDiagNat m i * x j else 0) =
      (-wideC m * wideDiagNat m i) * ∑ j : Fin (wideDim m),
        if (i : ℕ) < (j : ℕ) then x j else 0 := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · simp only [hlt, if_true]
    · simp only [hlt, if_false, mul_zero]
  rw [hfactor]
  ring

lemma wideWitness_mulVec {m : ℕ} (hm : 2 ≤ m) (i : Fin (wideDim m)) :
    (wideTriangular m *ᵥ wideWitness m) i =
      if (i : ℕ) + 1 = wideDim m then 1 else 0 := by
  rw [wideTriangular_mulVec_apply]
  by_cases hi : (i : ℕ) + 1 = wideDim m
  · simp only [hi, if_true]
    have htail : (∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then
        wideWitness m j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hnot : ¬ (i : ℕ) < (j : ℕ) := by
        have := j.isLt
        omega
      simp [hnot]
    have hilast : (i : ℕ) = wideDim m - 1 := by omega
    have hd : wideDiagNat m i ≠ 0 := (wideDiag_pos hm i).ne'
    have hw : wideWitness m i = 1 / wideDiagNat m (wideDim m - 1) := by
      simp [wideWitness, hi]
    have hdeq : wideDiagNat m (wideDim m - 1) = wideDiagNat m i := by
      congr 1
      exact hilast.symm
    rw [htail, hw, hdeq]
    simp only [mul_zero, sub_zero]
    field_simp [hd]
  · simp only [hi, if_false]
    have hi' : (i : ℕ) + 1 < wideDim m := by
      have := i.isLt
      omega
    have ht : wideDim m - 1 - (i : ℕ) < wideDim m := by omega
    have hs := wideWitness_suffix hm (wideDim m - 1 - (i : ℕ)) ht
    have hback : wideDim m - 1 - (wideDim m - 1 - (i : ℕ)) = (i : ℕ) := by omega
    have htail : (∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then
        wideWitness m j else 0) =
        (1 + wideC m) ^ (wideDim m - 2 - (i : ℕ)) /
          wideDiagNat m (wideDim m - 1) := by
      have hrewrite : (∑ j : Fin (wideDim m), if wideDim m - 1 -
          (wideDim m - 1 - (i : ℕ)) < (j : ℕ) then wideWitness m j else 0) =
          ∑ j : Fin (wideDim m), if (i : ℕ) < (j : ℕ) then wideWitness m j else 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [hback]
      rw [← hrewrite, hs]
      have htne : wideDim m - 1 - (i : ℕ) ≠ 0 := by omega
      simp only [htne, if_false]
      have hexp : wideDim m - 1 - (i : ℕ) - 1 = wideDim m - 2 - (i : ℕ) := by omega
      rw [hexp]
    have hw : wideWitness m i =
        wideC m * (1 + wideC m) ^ (wideDim m - 2 - (i : ℕ)) /
          wideDiagNat m (wideDim m - 1) := by
      simp [wideWitness, hi]
    have hd : wideDiagNat m (wideDim m - 1) ≠ 0 := (wideDiag_pos hm _).ne'
    rw [htail, hw]
    field_simp [hd]
    ring

lemma wideWitness_image_energy {m : ℕ} (hm : 2 ≤ m) :
    vecEnergy (wideTriangular m *ᵥ wideWitness m) = 1 := by
  have hk := wide_two_le_dim hm
  let last : Fin (wideDim m) := ⟨wideDim m - 1, by omega⟩
  unfold vecEnergy
  rw [sum_eq_single last]
  · have hi : (last : ℕ) + 1 = wideDim m := by
      simp [last]
      omega
    simp [wideWitness_mulVec hm last, hi]
  · intro i _ hne
    have hnot : ¬ (i : ℕ) + 1 = wideDim m := by
      intro h
      apply hne
      ext
      simp [last]
      omega
    simp [wideWitness_mulVec hm i, hnot]
  · simp

lemma vecEnergy_single_le {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    v i ^ 2 ≤ vecEnergy v := by
  unfold vecEnergy
  exact single_le_sum (fun _ _ => sq_nonneg _) (mem_univ i)

lemma wideWitness_energy_lower {m : ℕ} (hm : 2 ≤ m) :
    wideGrowthLower m ^ 2 ≤ vecEnergy (wideWitness m) := by
  have hhead := wideWitness_head_lower hm
  have hpos : 0 ≤ wideGrowthLower m := wideGrowthLower_nonneg (by omega)
  have hsq : wideGrowthLower m ^ 2 ≤
      wideWitness m ⟨0, wideDim_pos hm⟩ ^ 2 :=
    pow_le_pow_left₀ hpos hhead 2
  exact hsq.trans (vecEnergy_single_le _ _)

lemma widePrefix_card {n t : ℕ} (ht : t ≤ n) : (widePrefix n t).card = t := by
  classical
  let e : Fin t ↪ Fin n := ⟨fun i => Fin.castLE ht i, Fin.castLE_injective ht⟩
  have himage : (univ : Finset (Fin t)).map e = widePrefix n t := by
    ext j
    constructor
    · intro hj
      obtain ⟨i, _, rfl⟩ := mem_map.mp hj
      simp [widePrefix, e]
    · intro hj
      rw [widePrefix, mem_filter] at hj
      obtain ⟨_, hlt⟩ := hj
      refine mem_map.mpr ⟨⟨(j : ℕ), hlt⟩, mem_univ _, ?_⟩
      apply Fin.ext
      simp [e]
  rw [← himage, card_map, card_univ, Fintype.card_fin]

lemma widePrefix_orderEmb {n t : ℕ} (ht : t ≤ n) (j : Fin t) :
    (widePrefix n t).orderEmbOfFin (widePrefix_card ht) j = Fin.castLE ht j := by
  have hmem : ∀ i : Fin t, (Fin.castLE ht i : Fin n) ∈ widePrefix n t := by
    intro i
    rw [widePrefix, mem_filter]
    exact ⟨mem_univ _, i.isLt⟩
  have hmono : StrictMono (fun i : Fin t => (Fin.castLE ht i : Fin n)) := by
    intro a b h
    rw [Fin.lt_def] at h ⊢
    exact h
  have hfun := orderEmbOfFin_unique (widePrefix_card ht) hmem hmono
  exact congrFun hfun.symm j

lemma selectedCols_widePrefix_apply {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ) (i : Fin k)
    (j : Fin (widePrefix n k).card) :
    selectedCols A (widePrefix n k) i j =
      A i (Fin.castLE hkn (Fin.cast (widePrefix_card hkn) j)) := by
  simp only [selectedCols, Matrix.submatrix_apply, id_eq]
  have hord := widePrefix_orderEmb hkn (Fin.cast (widePrefix_card hkn) j)
  have heq : (widePrefix n k).orderEmbOfFin rfl j =
      (widePrefix n k).orderEmbOfFin (widePrefix_card hkn)
        (Fin.cast (widePrefix_card hkn) j) :=
    (orderEmbOfFin_eq_orderEmbOfFin_iff).2 (by simp)
  rw [heq, hord]

lemma vecEnergy_finCast {a b : ℕ} (h : a = b) (v : Fin b → ℝ) :
    vecEnergy (fun j : Fin a => v (Fin.cast h j)) = vecEnergy v := by
  unfold vecEnergy
  simpa using (finCongr h).sum_comp (fun j => v j ^ 2)

/-- Every `m ≥ 2` has a Parseval frame, the literal CPQR prefix, and a
selected coordinate whose inverse energy is at least the geometric scale. -/
theorem wide_adverse_family {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      ∃ x : Fin (widePrefix (wideWidth m) (wideDim m)).card → ℝ,
        OrthogonalRows A ∧
        (∀ i j : Fin (wideDim m),
          A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        vecEnergy (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x) = 1 ∧
        wideGrowthLower m ^ 2 ≤ vecEnergy x := by
  obtain ⟨A, hA, hR, hset, _hE⟩ := wide_frame_pivots hm
  have hkn : wideDim m ≤ wideWidth m := Nat.le_add_right _ _
  let J := widePrefix (wideWidth m) (wideDim m)
  let hcard : J.card = wideDim m := widePrefix_card hkn
  let y : Fin (wideDim m) → ℝ := wideWitness m
  let x : Fin J.card → ℝ := fun j => y (Fin.cast hcard j)
  have hcast : ∀ j : Fin (wideDim m),
      Fin.castLE hkn j = j.castAdd (wideDim m * wideRepeats m) := fun _ => rfl
  have hmul : selectedCols A J *ᵥ x = wideTriangular m *ᵥ y := by
    ext i
    simp only [Matrix.mulVec, dotProduct_eq]
    refine Fintype.sum_equiv (finCongr hcard)
      (fun j => selectedCols A J i j * x j)
      (fun j => wideTriangular m i j * y j) ?_
    intro j
    rw [selectedCols_widePrefix_apply hkn]
    rw [hcast (Fin.cast hcard j), hR]
    simp [x, y]
  refine ⟨A, x, hA, hR, hset, ?_, ?_⟩
  · rw [hmul]
    exact wideWitness_image_energy hm
  · rw [show vecEnergy x = vecEnergy y by
      simpa [x, y] using vecEnergy_finCast hcard y]
    exact wideWitness_energy_lower hm

lemma wide_total_nat {m : ℕ} :
    wideWidth m + wideDim m + 1 = 32 * (m * m) ^ 4 + 2 * (m * m) + 1 := by
  unfold wideWidth wideRepeats wideDim
  have hpow : ∀ a : ℕ, a ^ 4 = a * a ^ 3 := fun a => by
    simpa [Nat.succ_eq_add_one] using (pow_succ' a 3)
  rw [hpow (m * m)]
  ring

lemma wide_total_le {m : ℕ} (hm : 2 ≤ m) :
    ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ≤ 35 * (m : ℝ) ^ 8 := by
  rw [wide_total_nat]
  push_cast
  have hsqm : (m : ℝ) * (m : ℝ) = (m : ℝ) ^ 2 := by ring
  rw [hsqm]
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 8 := pow_le_pow_right₀ hM (by omega)
  have hone : (1 : ℝ) ≤ (m : ℝ) ^ 8 := by
    simpa using pow_le_pow_right₀ hM (by omega : 0 ≤ 8)
  have htwo : 2 * (m : ℝ) ^ 2 ≤ 2 * (m : ℝ) ^ 8 := by
    gcongr
  have heq : ((m : ℝ) ^ 2) ^ 4 = (m : ℝ) ^ 8 := by
    rw [← pow_mul, show 2 * 4 = 8 by norm_num]
  calc
    32 * ((m : ℝ) ^ 2) ^ 4 + 2 * (m : ℝ) ^ 2 + 1
        ≤ 32 * (m : ℝ) ^ 8 + 2 * (m : ℝ) ^ 8 + (m : ℝ) ^ 8 := by
          rw [heq]
          gcongr
    _ = 35 * (m : ℝ) ^ 8 := by ring

lemma wideGrowthLower_sq {m : ℕ} (hm : 1 ≤ m) :
    wideGrowthLower m ^ 2 =
      ((m : ℝ) ^ 2 / 4) * ((16 : ℝ) / 9) ^ m := by
  unfold wideGrowthLower
  have hrec : ((16 : ℝ) / 9) * ((16 : ℝ) / 9) ^ (m - 1) = ((16 : ℝ) / 9) ^ m := by
    rw [mul_comm]
    conv_rhs => rw [← Nat.sub_add_cancel hm]
    exact (pow_succ ((16 : ℝ) / 9) (m - 1)).symm
  have hsq : (((4 : ℝ) / 3) ^ (m - 1)) ^ 2 = ((16 : ℝ) / 9) ^ (m - 1) := by
    rw [pow_right_comm]
    congr 1
    norm_num
  have hfactor : (4 * (m : ℝ) ^ 2 / 9) =
      ((m : ℝ) ^ 2 / 4) * ((16 : ℝ) / 9) := by
    field_simp
    ring
  calc
    ((2 * (m : ℝ) / 3) * ((4 : ℝ) / 3) ^ (m - 1)) ^ 2
        = (2 * (m : ℝ) / 3) ^ 2 * (((4 : ℝ) / 3) ^ (m - 1)) ^ 2 := by ring
    _ = (4 * (m : ℝ) ^ 2 / 9) * ((16 : ℝ) / 9) ^ (m - 1) := by
          rw [hsq]
          ring
    _ = (((m : ℝ) ^ 2 / 4) * ((16 : ℝ) / 9)) * ((16 : ℝ) / 9) ^ (m - 1) := by
          rw [hfactor]
    _ = ((m : ℝ) ^ 2 / 4) * (((16 : ℝ) / 9) * ((16 : ℝ) / 9) ^ (m - 1)) := by ring
    _ = ((m : ℝ) ^ 2 / 4) * ((16 : ℝ) / 9) ^ m := by rw [hrec]

lemma ratio_step {p : ℕ} {n : ℕ} (hn : max (8 * p) 2 ≤ n) :
    ((16 : ℝ) / 9) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ p ≥
      (14 / 9) * (((16 : ℝ) / 9) ^ n / (n : ℝ) ^ p) := by
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hn0 : (0 : ℝ) < (n : ℕ) := by
    have : 0 < n := by
      have h2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
      omega
    exact_mod_cast this
  have hden : 8 * p ≤ n + 1 := by
    have h8 : 8 * p ≤ n := le_trans (Nat.le_max_left _ _) hn
    omega
  have hfrac : (p : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (1 : ℝ) / 8 := by
    rw [div_le_div_iff₀ hn1 (by norm_num : (0 : ℝ) < 8)]
    have h8 : (8 : ℝ) * (p : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hden
    linarith
  have ha : (-2 : ℝ) ≤ -1 / ((n + 1 : ℕ) : ℝ) := by
    have hle : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    calc
      (-2 : ℝ) ≤ -1 := by norm_num
      _ ≤ -(1 / ((n + 1 : ℕ) : ℝ)) := by
          apply neg_le_neg
          rw [div_le_one hn1]
          exact hle
      _ = -1 / ((n + 1 : ℕ) : ℝ) := by ring
  have hber := one_add_mul_le_pow (a := -1 / ((n + 1 : ℕ) : ℝ)) ha p
  have hbase : (1 : ℝ) + -1 / ((n + 1 : ℕ) : ℝ) = (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    field_simp [hn1.ne']
    norm_cast
    omega
  have hlin : (1 : ℝ) - (p : ℝ) / ((n + 1 : ℕ) : ℝ) ≤
      ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ p := by
    have hre : (1 : ℝ) + (p : ℝ) * (-1 / ((n + 1 : ℕ) : ℝ)) =
        (1 : ℝ) - (p : ℝ) / ((n + 1 : ℕ) : ℝ) := by ring
    rw [← hre, ← hbase]
    exact hber
  have hseven : (7 : ℝ) / 8 ≤
      ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ p := by
    exact le_trans (by linarith) hlin
  have hmul : (14 / 9) * ((n + 1 : ℕ) : ℝ) ^ p ≤
      ((16 : ℝ) / 9) * (n : ℝ) ^ p := by
    have h78 : (7 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ p ≤ (8 : ℝ) * (n : ℝ) ^ p := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ p := by positivity
      have hrewrite : (7 : ℝ) / 8 ≤ ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ p := hseven
      rw [div_pow] at hrewrite
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8)] at hrewrite
      -- (7/8) * (n+1)^p ≤ n^p, so 7*(n+1)^p ≤ 8*n^p
      have h8pos : (0 : ℝ) < 8 := by norm_num
      -- restart from hseven more directly
      have hdirect : (7 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ p ≤ (8 : ℝ) * (n : ℝ) ^ p := by
        have hge := hseven
        rw [div_pow] at hge
        have hdenp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ p := by positivity
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hdenp] at hge
        simpa [mul_comm, mul_left_comm, mul_assoc] using hge
      exact hdirect
    calc
      (14 / 9) * ((n + 1 : ℕ) : ℝ) ^ p
          = (2 / 9) * (7 * ((n + 1 : ℕ) : ℝ) ^ p) := by ring
      _ ≤ (2 / 9) * (8 * (n : ℝ) ^ p) := by
            gcongr
      _ = ((16 : ℝ) / 9) * (n : ℝ) ^ p := by ring
  have hpos16 : (0 : ℝ) < ((16 : ℝ) / 9) ^ n := by positivity
  calc
    (14 / 9) * (((16 : ℝ) / 9) ^ n / (n : ℝ) ^ p)
        = (((16 : ℝ) / 9) ^ n * ((14 / 9) * ((n + 1 : ℕ) : ℝ) ^ p)) /
            ((n : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p) := by
          field_simp
    _ ≤ (((16 : ℝ) / 9) ^ n * (((16 : ℝ) / 9) * (n : ℝ) ^ p)) /
          ((n : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p) := by
          gcongr
    _ = ((16 : ℝ) / 9) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) ^ p := by
          rw [pow_succ]
          field_simp

lemma geometric_growth (p t : ℕ) :
    let M := max (8 * p) 2
    ((16 : ℝ) / 9) ^ (M + t) / ((M + t : ℕ) : ℝ) ^ p ≥
      ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * ((14 : ℝ) / 9) ^ t := by
  intro M
  induction t with
  | zero =>
    simp [M]
  | succ t ih =>
    have hstep := ratio_step (p := p) (n := M + t) (by
      dsimp [M]
      omega)
    calc
      ((16 : ℝ) / 9) ^ (M + (t + 1)) / ((M + (t + 1) : ℕ) : ℝ) ^ p
          = ((16 : ℝ) / 9) ^ ((M + t) + 1) / (((M + t) + 1 : ℕ) : ℝ) ^ p := rfl
      _ ≥ (14 / 9) * (((16 : ℝ) / 9) ^ (M + t) / ((M + t : ℕ) : ℝ) ^ p) := hstep
      _ ≥ (14 / 9) * (((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * ((14 : ℝ) / 9) ^ t) := by
            gcongr
      _ = ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * ((14 : ℝ) / 9) ^ (t + 1) := by
            rw [pow_succ]
            ring

lemma exists_scale_beats_polynomial (d : ℕ) {C : ℝ} (hC : 0 < C) (mMin : ℕ) :
    ∃ m : ℕ, max mMin 2 ≤ m ∧
      C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) <
        wideGrowthLower m ^ 2 := by
  let p := 16 * d
  let K := C * (35 : ℝ) ^ (2 * d)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let M := max (8 * p) 2
  have hM2 : 2 ≤ M := le_max_right _ _
  let Q := K * (M : ℝ) ^ p * ((9 : ℝ) / 16) ^ M
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  obtain ⟨t0, ht0⟩ := exists_nat_gt (Q * 9 / 5)
  let t := max t0 mMin
  have ht : Q * 9 / 5 < (t : ℝ) :=
    lt_of_lt_of_le ht0 (by exact_mod_cast le_max_left t0 mMin)
  have hgeom : ((14 : ℝ) / 9) ^ t > Q := by
    have hber := one_add_mul_le_pow (a := (5 : ℝ) / 9) (by norm_num) t
    have hlin : Q < 1 + (t : ℝ) * (5 / 9) := by
      have hmul : Q < (t : ℝ) * (5 / 9) := by
        have h5 : (0 : ℝ) < 5 / 9 := by norm_num
        have ht' : Q * 9 / 5 < (t : ℝ) := ht
        nlinarith
      linarith
    have hbase : (1 : ℝ) + 5 / 9 = 14 / 9 := by norm_num
    have hpow : 1 + (t : ℝ) * (5 / 9) ≤ ((14 : ℝ) / 9) ^ t := by
      simpa [hbase] using hber
    exact lt_of_lt_of_le hlin hpow
  let m := M + t
  have hm2 : 2 ≤ m := le_trans hM2 (Nat.le_add_right _ _)
  have hm : max mMin 2 ≤ m :=
    max_le (le_trans (le_max_right t0 mMin) (Nat.le_add_left t M))
      (le_trans hM2 (Nat.le_add_right M t))
  have hgrowth := geometric_growth p t
  have hu : K < ((16 : ℝ) / 9) ^ m / (m : ℝ) ^ p := by
    have hlower := hgrowth
    dsimp [M] at hlower
    have hpos : 0 < ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p := by positivity
    have hmul : ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * Q <
        ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * ((14 : ℝ) / 9) ^ t :=
      mul_lt_mul_of_pos_left hgeom hpos
    have hcancel : ((16 : ℝ) / 9) ^ M * ((9 : ℝ) / 16) ^ M = 1 := by
      rw [← mul_pow]
      norm_num
    have hMp : (M : ℝ) ^ p ≠ 0 := by positivity
    have hQeq : ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * Q = K := by
      dsimp [Q]
      calc
        ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p *
            (K * (M : ℝ) ^ p * ((9 : ℝ) / 16) ^ M)
          = K * (((16 : ℝ) / 9) ^ M * ((9 : ℝ) / 16) ^ M) *
              ((M : ℝ) ^ p / (M : ℝ) ^ p) := by
            field_simp [hMp]
        _ = K := by
            rw [hcancel, div_self hMp]
            ring
    have hge : ((16 : ℝ) / 9) ^ M / (M : ℝ) ^ p * ((14 : ℝ) / 9) ^ t ≤
        ((16 : ℝ) / 9) ^ m / (m : ℝ) ^ p := by
      simpa [m, M] using hlower
    linarith
  have hpow : K * (m : ℝ) ^ p < ((16 : ℝ) / 9) ^ m := by
    have hmpos : (0 : ℝ) < (m : ℝ) ^ p := by positivity
    rw [lt_div_iff₀ hmpos] at hu
    exact hu
  have hcoef : (1 : ℝ) ≤ (m : ℝ) ^ 2 / 4 := by
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    nlinarith
  have hsq : ((16 : ℝ) / 9) ^ m ≤ wideGrowthLower m ^ 2 := by
    rw [wideGrowthLower_sq (by omega)]
    calc
      ((16 : ℝ) / 9) ^ m = 1 * ((16 : ℝ) / 9) ^ m := by ring
      _ ≤ (m : ℝ) ^ 2 / 4 * ((16 : ℝ) / 9) ^ m :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hN : ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) ≤
      (35 * (m : ℝ) ^ 8) ^ (2 * d) := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (wide_total_le hm2) _
  have hsplit : (35 * (m : ℝ) ^ 8) ^ (2 * d) =
      (35 : ℝ) ^ (2 * d) * (m : ℝ) ^ p := by
    dsimp [p]
    rw [mul_pow, ← pow_mul]
    congr 1
    ring
  refine ⟨m, hm, ?_⟩
  calc
    C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d)
        ≤ C * (35 * (m : ℝ) ^ 8) ^ (2 * d) :=
          mul_le_mul_of_nonneg_left hN hC.le
    _ = K * (m : ℝ) ^ p := by
          rw [hsplit]
          dsimp [K]
          exact (mul_assoc _ _ _).symm
    _ < ((16 : ℝ) / 9) ^ m := hpow
    _ ≤ wideGrowthLower m ^ 2 := hsq

/-- For every degree and every positive coefficient, some orthogonal-row
frame makes the actual CPQR block beat that polynomial. -/
theorem cpqr_no_joint_polynomial (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x := by
  obtain ⟨m, hm, hpoly⟩ := exists_scale_beats_polynomial d hC 0
  have hm2 : 2 ≤ m := (le_max_right (0 : ℕ) 2).trans hm
  obtain ⟨A, x, hA, _, hset, hAx, hx⟩ := wide_adverse_family hm2
  refine ⟨wideDim m, wideWidth m, A, ?_⟩
  rw [hset]
  refine ⟨x, hA, ?_⟩
  calc
    C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) *
        vecEnergy (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x)
        = C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) := by
          rw [hAx]
          ring
    _ < wideGrowthLower m ^ 2 := hpoly
    _ ≤ vecEnergy x := hx

lemma named_polynomial_sq_le (k n : ℕ) :
    (max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
      (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2))) ^ 2 ≤
      ((n + k + 1 : ℕ) : ℝ) ^ 8 := by
  set N : ℝ := ((n + k + 1 : ℕ) : ℝ)
  have hN1 : (1 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ (n + k + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ n + k + 1 by omega)
    simpa [N] using this
  have hn : (n : ℝ) ≤ N := by
    have : (n : ℝ) ≤ (n + k + 1 : ℕ) := by
      exact_mod_cast (show n ≤ n + k + 1 by omega)
    simpa [N] using this
  have hk : (k : ℝ) ≤ N := by
    have : (k : ℝ) ≤ (n + k + 1 : ℕ) := by
      exact_mod_cast (show k ≤ n + k + 1 by omega)
    simpa [N] using this
  have ht : ((n - k + 1 : ℕ) : ℝ) ≤ N := by
    have : ((n - k + 1 : ℕ) : ℝ) ≤ (n + k + 1 : ℕ) := by
      exact_mod_cast (show n - k + 1 ≤ n + k + 1 by omega)
    simpa [N] using this
  have hN0 : 0 ≤ N := by positivity
  have hn3 : (n : ℝ) ^ 3 ≤ N ^ 4 := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg n) hn 3).trans
      (pow_le_pow_right₀ hN1 (by omega))
  have hk3 : (k : ℝ) ^ 3 ≤ N ^ 4 := by
    exact (pow_le_pow_left₀ (Nat.cast_nonneg k) hk 3).trans
      (pow_le_pow_right₀ hN1 (by omega))
  have hprod : (k : ℝ) * ((n - k + 1 : ℕ) : ℝ) ≤ N ^ 2 := by
    have := mul_le_mul hk ht (Nat.cast_nonneg _) hN0
    simpa [pow_two] using this
  have hsq : ((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2 ≤ N ^ 4 := by
    have h0 : 0 ≤ (k : ℝ) * ((n - k + 1 : ℕ) : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hsq' := pow_le_pow_left₀ h0 hprod 2
    calc
      ((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2 ≤ (N ^ 2) ^ 2 := hsq'
      _ = N ^ 4 := by ring
  have hmax : max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
      (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2)) ≤ N ^ 4 := by
    exact max_le hn3 (max_le hk3 hsq)
  have hmax0 : 0 ≤ max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
      (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2)) := by
    positivity
  have hsqmax := pow_le_pow_left₀ hmax0 hmax 2
  have hpow : (N ^ 4) ^ 2 = N ^ 8 := by ring
  exact hsqmax.trans_eq hpow

/-- The geometric family beats the campaign's named polynomial. -/
theorem cpqr_named_polynomial_obstruction :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
          (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2))) ^ 2 *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x := by
  obtain ⟨k, n, A, x, hA, hlt⟩ := cpqr_no_joint_polynomial 4 (by norm_num : (0 : ℝ) < 1)
  refine ⟨k, n, A, x, hA, ?_⟩
  have hbound := named_polynomial_sq_le k n
  have he : 0 ≤ vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) := vecEnergy_nonneg _
  calc
    (max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
        (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2))) ^ 2 *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x)
      ≤ ((n + k + 1 : ℕ) : ℝ) ^ 8 *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
        mul_le_mul_of_nonneg_right hbound he
    _ = (1 : ℝ) * ((n + k + 1 : ℕ) : ℝ) ^ (2 * 4) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) := by ring
    _ < vecEnergy x := hlt

end StructuredColumnSelection
