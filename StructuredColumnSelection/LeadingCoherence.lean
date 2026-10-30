import StructuredColumnSelection.ScaledDesignFrame
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators

/-!
# Leading–leading coherence of the scaled triangular block

Columns of `wideTriangular m` are supported on rows `l ≤ t`. For `i < j`
the inner product is `-wideC m * diag_i ^ 2` plus the shared off-diagonal
energy `S_i`, and both column energies sit strictly above
`wideAlpha m ^ 2 / 4 + S_i`. The resulting ratio is at most `1/2 + 1/m`.
Scaling by `3` multiplies inner products and energies by `9`, so
`scaledBlock m` obeys the same bound.

This does not bound filler pairs. A leading–leading ratio `≤ 1/2 + 1/m`
is not a coherence bound on the whole frame. This does not close outcome 3,
and it is not a polynomial CPQR bound.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-- Off-diagonal column energy `wideC m ^ 2 * ∑_{l < i} (wideDiagNat m l) ^ 2`. -/
noncomputable def wideColumnTail (m i : ℕ) : ℝ :=
  wideC m ^ 2 * ∑ l ∈ Finset.range i, (wideDiagNat m l) ^ 2

lemma wideColumnTail_nonneg (m i : ℕ) : 0 ≤ wideColumnTail m i := by
  unfold wideColumnTail
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma wideC_le_one_div_two_m {m : ℕ} (hm : 2 ≤ m) :
    wideC m ≤ 1 / (2 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  unfold wideC
  rw [div_le_div_iff₀ (wideDen_pos m) (by positivity)]
  nlinarith

lemma wideDiag_sq_gt_quarter {m : ℕ} (hm : 2 ≤ m) {i : ℕ} (hi : i < wideDim m) :
    wideAlpha m ^ 2 / 4 < (wideDiagNat m i) ^ 2 := by
  have hhalf := wideDiag_half_lower hm hi
  have hpos : 0 < wideAlpha m / 2 := div_pos (wideAlpha_pos hm) (by norm_num)
  have hdiag : 0 < wideDiagNat m i := wideDiag_pos hm i
  have h1 : (wideAlpha m / 2) * (wideAlpha m / 2) <
      wideDiagNat m i * (wideAlpha m / 2) :=
    mul_lt_mul_of_pos_right hhalf hpos
  have h2 : wideDiagNat m i * (wideAlpha m / 2) <
      wideDiagNat m i * wideDiagNat m i :=
    mul_lt_mul_of_pos_left hhalf hdiag
  have hsq : (wideAlpha m / 2) ^ 2 < (wideDiagNat m i) ^ 2 := by
    rw [pow_two, pow_two]
    exact h1.trans h2
  have heq : (wideAlpha m / 2) ^ 2 = wideAlpha m ^ 2 / 4 := by ring
  linarith

lemma wideColumnTail_mono {i j : ℕ} (hij : i ≤ j) (m : ℕ) :
    wideColumnTail m i ≤ wideColumnTail m j := by
  unfold wideColumnTail
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) ?_
  intro _ _ _
  exact sq_nonneg _

/-- `S_i ≤ wideAlpha m ^ 2 / 4`, from `diag ≤ wideAlpha` and `k * wideC ^ 2 ≤ 1/4`. -/
lemma wideColumn_tailSum_le {m : ℕ} (hm : 2 ≤ m) {i : ℕ} (hi : i ≤ wideDim m) :
    wideColumnTail m i ≤ wideAlpha m ^ 2 / 4 := by
  have hα2 : 0 ≤ wideAlpha m ^ 2 := sq_nonneg _
  have hterms : ∀ l ∈ Finset.range i, (wideDiagNat m l) ^ 2 ≤ wideAlpha m ^ 2 := by
    intro l _
    have hd := wideDiag_pos hm l
    have hda := wideDiag_le_alpha hm l
    nlinarith
  have hsum : ∑ l ∈ Finset.range i, (wideDiagNat m l) ^ 2 ≤
      (wideDim m : ℝ) * wideAlpha m ^ 2 := by
    calc ∑ l ∈ Finset.range i, (wideDiagNat m l) ^ 2
        ≤ ∑ _l ∈ Finset.range i, wideAlpha m ^ 2 := Finset.sum_le_sum hterms
      _ = (i : ℝ) * wideAlpha m ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (wideDim m : ℝ) * wideAlpha m ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hα2
  unfold wideColumnTail
  calc wideC m ^ 2 * ∑ l ∈ Finset.range i, (wideDiagNat m l) ^ 2
      ≤ wideC m ^ 2 * ((wideDim m : ℝ) * wideAlpha m ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = ((wideDim m : ℝ) * wideC m ^ 2) * wideAlpha m ^ 2 := by ring
    _ ≤ (1 / 4) * wideAlpha m ^ 2 :=
        mul_le_mul_of_nonneg_right (wide_kc_sq_le hm) hα2
    _ = wideAlpha m ^ 2 / 4 := by ring

/-- Sum of a function that vanishes strictly above index `t`. -/
lemma sum_below_diag {k : ℕ} {t : ℕ} (ht : t < k) (head : ℕ → ℝ) (mid : ℝ) :
    ∑ l : Fin k,
        (if (l : ℕ) < t then head l else if (l : ℕ) = t then mid else 0) =
      (∑ l ∈ Finset.range t, head l) + mid := by
  let f : ℕ → ℝ := fun n => if n < t then head n else if n = t then mid else 0
  have hcoe : ∑ l : Fin k, (if (l : ℕ) < t then head l else if (l : ℕ) = t then mid else 0) =
      ∑ l : Fin k, f l := rfl
  rw [hcoe, Fin.sum_univ_eq_sum_range f k]
  have hk : t + 1 ≤ k := by omega
  rw [← Finset.sum_range_add_sum_Ico f hk]
  have htail : ∑ n ∈ Finset.Ico (t + 1) k, f n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have h1 : t + 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hlt : ¬ n < t := by omega
    have hne : n ≠ t := by omega
    simp [f, hlt, hne]
  rw [htail, add_zero, Finset.sum_range_succ]
  have hhead : ∑ n ∈ Finset.range t, f n = ∑ n ∈ Finset.range t, head n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [f, Finset.mem_range.mp hn]
  have hmid : f t = mid := by
    simp [f]
  rw [hhead, hmid]

lemma wideColumn_row_mul {m : ℕ} {i j : Fin (wideDim m)} (hij : (i : ℕ) < (j : ℕ))
    (l : Fin (wideDim m)) :
    wideTriangular m l i * wideTriangular m l j =
      if (l : ℕ) < (i : ℕ) then wideC m ^ 2 * (wideDiagNat m l) ^ 2
      else if (l : ℕ) = (i : ℕ) then -wideC m * (wideDiagNat m i) ^ 2
      else 0 := by
  by_cases hl : (l : ℕ) < (i : ℕ)
  · have hne : l ≠ i := fun h => by subst h; omega
    have hlj : (l : ℕ) < (j : ℕ) := by omega
    have hnej : l ≠ j := fun h => by subst h; omega
    rw [if_pos hl]
    unfold wideTriangular
    rw [if_neg hne, if_pos hl, if_neg hnej, if_pos hlj]
    ring
  · by_cases heq : (l : ℕ) = (i : ℕ)
    · have hli : l = i := Fin.ext heq
      subst l
      have hne : i ≠ j := fun h => by subst h; omega
      rw [if_neg hl, if_pos heq, wideTriangular_diag]
      unfold wideTriangular
      rw [if_neg hne, if_pos hij]
      ring
    · have hgt : (i : ℕ) < (l : ℕ) := by omega
      rw [if_neg hl, if_neg heq, wideTriangular_upper hgt, zero_mul]

lemma wideColumn_inner {m : ℕ} {i j : Fin (wideDim m)} (hij : (i : ℕ) < (j : ℕ)) :
    (fun row => wideTriangular m row i) ⬝ᵥ (fun row => wideTriangular m row j) =
      -wideC m * (wideDiagNat m i) ^ 2 + wideColumnTail m (i : ℕ) := by
  rw [dotProduct]
  simp_rw [wideColumn_row_mul hij]
  rw [sum_below_diag i.isLt
    (fun n => wideC m ^ 2 * (wideDiagNat m n) ^ 2)
    (-wideC m * (wideDiagNat m (i : ℕ)) ^ 2)]
  unfold wideColumnTail
  rw [← Finset.mul_sum]
  ring

lemma wideColumn_row_sq {m : ℕ} (j l : Fin (wideDim m)) :
    (wideTriangular m l j) ^ 2 =
      if (l : ℕ) < (j : ℕ) then wideC m ^ 2 * (wideDiagNat m l) ^ 2
      else if (l : ℕ) = (j : ℕ) then (wideDiagNat m j) ^ 2
      else 0 := by
  by_cases hl : (l : ℕ) < (j : ℕ)
  · have hne : l ≠ j := fun h => by subst h; omega
    rw [if_pos hl]
    unfold wideTriangular
    rw [if_neg hne, if_pos hl]
    ring
  · by_cases heq : (l : ℕ) = (j : ℕ)
    · have hlj : l = j := Fin.ext heq
      subst l
      rw [if_neg hl, if_pos heq, wideTriangular_diag]
    · have hgt : (j : ℕ) < (l : ℕ) := by omega
      rw [if_neg hl, if_neg heq, wideTriangular_upper hgt]
      simp

lemma wideColumn_energy {m : ℕ} (j : Fin (wideDim m)) :
    vecEnergy (fun row => wideTriangular m row j) =
      (wideDiagNat m j) ^ 2 + wideColumnTail m (j : ℕ) := by
  unfold vecEnergy
  simp_rw [wideColumn_row_sq j]
  rw [sum_below_diag j.isLt
    (fun n => wideC m ^ 2 * (wideDiagNat m n) ^ 2)
    ((wideDiagNat m (j : ℕ)) ^ 2)]
  unfold wideColumnTail
  rw [← Finset.mul_sum]
  ring

/-- For `0 ≤ c ≤ 1/4` and `s ≤ a/4`, `(c a + s) / (a/4 + s) ≤ 1/2 + 2c`. -/
lemma tail_ratio_le {c s a : ℝ} (hc : c ≤ 1 / 4) (hs : s ≤ a / 4) :
    c * a + s ≤ (1 / 2 + 2 * c) * (a / 4 + s) := by
  have hdiff : (1 / 2 + 2 * c) * (a / 4 + s) - (c * a + s) =
      ((1 / 2 - 2 * c) * (a - 4 * s)) / 4 := by ring
  have hnn : 0 ≤ (1 / 2 - 2 * c) * (a - 4 * s) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have : 0 ≤ ((1 / 2 - 2 * c) * (a - 4 * s)) / 4 := div_nonneg hnn h4
  linarith

lemma col_dot_smul {n : ℕ} (s : ℝ) (v w : Fin n → ℝ) :
    (s • v) ⬝ᵥ (s • w) = s ^ 2 * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i, (s * v i) * (s * w i) = s ^ 2 * (v i * w i) := fun i => by ring
  simp_rw [hterm]
  rw [Finset.mul_sum]

lemma vecEnergy_const_smul {n : ℕ} (s : ℝ) (v : Fin n → ℝ) :
    vecEnergy (s • v) = s ^ 2 * vecEnergy v := by
  unfold vecEnergy
  simp only [Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i, (s * v i) ^ 2 = s ^ 2 * (v i ^ 2) := fun i => by ring
  simp_rw [hterm]
  rw [Finset.mul_sum]

lemma sqrt_nine_mul (x : ℝ) :
    Real.sqrt ((3 : ℝ) ^ 2 * x) = 3 * Real.sqrt x := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 2) x, Real.sqrt_sq (by norm_num)]

lemma wide_leading_leading_ratio {m : ℕ} (hm : 2 ≤ m) {i j : Fin (wideDim m)}
    (hij : (i : ℕ) < (j : ℕ)) :
    |(fun row => wideTriangular m row i) ⬝ᵥ (fun row => wideTriangular m row j)| ≤
      (1 / 2 + 1 / (m : ℝ)) *
        (Real.sqrt (vecEnergy (fun row => wideTriangular m row i)) *
          Real.sqrt (vecEnergy (fun row => wideTriangular m row j))) := by
  have hcpos : 0 < wideC m := wideC_pos hm
  have h2c : 2 * wideC m ≤ 1 / (m : ℝ) := by
    calc 2 * wideC m
        ≤ 2 * (1 / (2 * (m : ℝ))) :=
          mul_le_mul_of_nonneg_left (wideC_le_one_div_two_m hm) (by norm_num)
      _ = 1 / (m : ℝ) := by ring
  have hc4 : wideC m ≤ 1 / 4 := by
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    calc wideC m ≤ 1 / (2 * (m : ℝ)) := wideC_le_one_div_two_m hm
      _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  set S : ℝ := wideColumnTail m (i : ℕ)
  have hS0 : 0 ≤ S := wideColumnTail_nonneg m (i : ℕ)
  have hSle : S ≤ wideAlpha m ^ 2 / 4 :=
    wideColumn_tailSum_le hm (Nat.le_of_lt i.isLt)
  have hSj : S ≤ wideColumnTail m (j : ℕ) := wideColumnTail_mono (Nat.le_of_lt hij) m
  have hdi : wideAlpha m ^ 2 / 4 < (wideDiagNat m (i : ℕ)) ^ 2 :=
    wideDiag_sq_gt_quarter hm i.isLt
  have hdj : wideAlpha m ^ 2 / 4 < (wideDiagNat m (j : ℕ)) ^ 2 :=
    wideDiag_sq_gt_quarter hm j.isLt
  have hd2 : (wideDiagNat m (i : ℕ)) ^ 2 ≤ wideAlpha m ^ 2 := by
    have hd := wideDiag_pos hm (i : ℕ)
    have hda := wideDiag_le_alpha hm (i : ℕ)
    nlinarith
  have habs : |-wideC m * (wideDiagNat m (i : ℕ)) ^ 2 + S| ≤
      wideC m * wideAlpha m ^ 2 + S := by
    calc |-wideC m * (wideDiagNat m (i : ℕ)) ^ 2 + S|
        ≤ |-wideC m * (wideDiagNat m (i : ℕ)) ^ 2| + |S| := abs_add_le _ _
      _ = wideC m * (wideDiagNat m (i : ℕ)) ^ 2 + S := by
          rw [neg_mul, abs_neg, abs_mul, abs_of_pos hcpos, abs_of_nonneg (sq_nonneg _),
            abs_of_nonneg hS0]
      _ ≤ wideC m * wideAlpha m ^ 2 + S := by
          have hmul := mul_le_mul_of_nonneg_left hd2 hcpos.le
          linarith
  set T : ℝ := wideAlpha m ^ 2 / 4 + S
  set Ei : ℝ := vecEnergy (fun row => wideTriangular m row i)
  set Ej : ℝ := vecEnergy (fun row => wideTriangular m row j)
  have hinner : (fun row => wideTriangular m row i) ⬝ᵥ (fun row => wideTriangular m row j) =
      -wideC m * (wideDiagNat m (i : ℕ)) ^ 2 + S := wideColumn_inner hij
  have hEi : Ei = (wideDiagNat m (i : ℕ)) ^ 2 + S := wideColumn_energy i
  have hEj : Ej = (wideDiagNat m (j : ℕ)) ^ 2 + wideColumnTail m (j : ℕ) :=
    wideColumn_energy j
  have hα := wideAlpha_pos hm
  have hquarter : 0 < wideAlpha m ^ 2 / 4 := div_pos (sq_pos_of_pos hα) (by norm_num)
  have hTpos : 0 < T := by
    change 0 < wideAlpha m ^ 2 / 4 + S
    linarith [hquarter, hS0]
  have hEi_gt : T < Ei := by
    rw [hEi]
    change wideAlpha m ^ 2 / 4 + S < _
    linarith [hdi]
  have hEj_gt : T < Ej := by
    rw [hEj]
    change wideAlpha m ^ 2 / 4 + S < _
    linarith [hdj, hSj]
  have hsq : T ^ 2 < Ei * Ej := by
    have h1 : T * T < Ei * T := mul_lt_mul_of_pos_right hEi_gt hTpos
    have hEi_pos : 0 < Ei := lt_trans hTpos hEi_gt
    have h2 : Ei * T < Ei * Ej := mul_lt_mul_of_pos_left hEj_gt hEi_pos
    have : T * T < Ei * Ej := h1.trans h2
    simpa [pow_two] using this
  have hgeom : T < Real.sqrt Ei * Real.sqrt Ej := by
    have hEi0 : 0 ≤ Ei := vecEnergy_nonneg _
    rw [← Real.sqrt_mul hEi0, ← Real.sqrt_sq hTpos.le]
    exact Real.sqrt_lt_sqrt (sq_nonneg T) (by simpa [pow_two] using hsq)
  have hN : |(fun row => wideTriangular m row i) ⬝ᵥ (fun row => wideTriangular m row j)| ≤
      wideC m * wideAlpha m ^ 2 + S := by
    rw [hinner]
    exact habs
  have hratio : wideC m * wideAlpha m ^ 2 + S ≤ (1 / 2 + 2 * wideC m) * T :=
    tail_ratio_le hc4 hSle
  have hρ : 1 / 2 + 2 * wideC m ≤ 1 / 2 + 1 / (m : ℝ) := by linarith
  have hρpos : 0 < 1 / 2 + 1 / (m : ℝ) := by positivity
  calc |(fun row => wideTriangular m row i) ⬝ᵥ (fun row => wideTriangular m row j)|
      ≤ wideC m * wideAlpha m ^ 2 + S := hN
    _ ≤ (1 / 2 + 2 * wideC m) * T := hratio
    _ ≤ (1 / 2 + 1 / (m : ℝ)) * T := mul_le_mul_of_nonneg_right hρ hTpos.le
    _ ≤ (1 / 2 + 1 / (m : ℝ)) * (Real.sqrt Ei * Real.sqrt Ej) :=
        le_of_lt (mul_lt_mul_of_pos_left hgeom hρpos)

lemma scaledBlock_column {m : ℕ} (j : Fin (wideDim m)) :
    (fun i => scaledBlock m i j) = (3 : ℝ) • fun i => wideTriangular m i j := by
  ext i
  simp [scaledBlock, Matrix.smul_apply, Pi.smul_apply]

/-- Leading columns of `scaledBlock m` have normalized coherence at most `1/2 + 1/m`. -/
theorem leading_leading_ratio {m : ℕ} (hm : 2 ≤ m) {i j : Fin (wideDim m)} (hij : i ≠ j) :
    |∑ row, scaledBlock m row i * scaledBlock m row j| ≤
      (1 / 2 + 1 / (m : ℝ)) *
        (Real.sqrt (vecEnergy (fun row => scaledBlock m row i)) *
          Real.sqrt (vecEnergy (fun row => scaledBlock m row j))) := by
  suffices hord : ∀ {a b : Fin (wideDim m)}, (a : ℕ) < (b : ℕ) →
      |∑ row, scaledBlock m row a * scaledBlock m row b| ≤
        (1 / 2 + 1 / (m : ℝ)) *
          (Real.sqrt (vecEnergy (fun row => scaledBlock m row a)) *
            Real.sqrt (vecEnergy (fun row => scaledBlock m row b))) by
    by_cases hlt : (i : ℕ) < (j : ℕ)
    · exact hord hlt
    · have hgt : (j : ℕ) < (i : ℕ) := by
        have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        omega
      have hswap := hord hgt
      have hsum : ∑ row, scaledBlock m row i * scaledBlock m row j =
          ∑ row, scaledBlock m row j * scaledBlock m row i := by
        refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
      rw [hsum, mul_comm (Real.sqrt (vecEnergy (fun row => scaledBlock m row i)))]
      exact hswap
  intro a b hab
  have hwide := wide_leading_leading_ratio hm hab
  have hcola := scaledBlock_column a
  have hcolb := scaledBlock_column b
  have hdot : ∑ row, scaledBlock m row a * scaledBlock m row b =
      ((3 : ℝ) ^ 2) * ((fun row => wideTriangular m row a) ⬝ᵥ
        (fun row => wideTriangular m row b)) := by
    rw [show ∑ row, scaledBlock m row a * scaledBlock m row b =
        (fun row => scaledBlock m row a) ⬝ᵥ (fun row => scaledBlock m row b) by
          simp [dotProduct]]
    rw [hcola, hcolb, col_dot_smul]
  have hEa : vecEnergy (fun row => scaledBlock m row a) =
      (3 : ℝ) ^ 2 * vecEnergy (fun row => wideTriangular m row a) := by
    rw [scaledBlock_column, vecEnergy_const_smul]
  have hEb : vecEnergy (fun row => scaledBlock m row b) =
      (3 : ℝ) ^ 2 * vecEnergy (fun row => wideTriangular m row b) := by
    rw [scaledBlock_column, vecEnergy_const_smul]
  have h9 : (0 : ℝ) ≤ (3 : ℝ) ^ 2 := by norm_num
  rw [hdot, hEa, hEb, sqrt_nine_mul, sqrt_nine_mul, abs_mul, abs_of_nonneg h9]
  calc (3 : ℝ) ^ 2 *
        |(fun row => wideTriangular m row a) ⬝ᵥ (fun row => wideTriangular m row b)|
      ≤ (3 : ℝ) ^ 2 * ((1 / 2 + 1 / (m : ℝ)) *
          (Real.sqrt (vecEnergy (fun row => wideTriangular m row a)) *
            Real.sqrt (vecEnergy (fun row => wideTriangular m row b)))) :=
        mul_le_mul_of_nonneg_left hwide h9
    _ = (1 / 2 + 1 / (m : ℝ)) *
          ((3 * Real.sqrt (vecEnergy (fun row => wideTriangular m row a))) *
            (3 * Real.sqrt (vecEnergy (fun row => wideTriangular m row b)))) := by ring

end StructuredColumnSelection
