import StructuredColumnSelection.StaticClass
import StructuredColumnSelection.WideCPQRGrowth

/-!
# Absolute incoherence does not restore a polynomial

Every column of an outcome-2 frame has energy at most `1 / (2k)`.
Cauchy–Schwarz then bounds every off-diagonal inner product by the same
number. For every `ρ > 0`, a large enough frame lies in
`ColumnIncoherent A ρ` and its CPQR block still beats every polynomial
`C (n + k + 1)^{2d}`.

`ColumnIncoherent` bounds absolute inner products. It is not the
normalized coherence ratio in SPEC §10. The case `ρ = 0` remains the
phase-P hypothesis, and the outcome-2 frame stays outside that case.
This does not close outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma wideTriangular_entry_sq {m : ℕ} (hm : 2 ≤ m) (i j : Fin (wideDim m)) :
    (wideTriangular m i j) ^ 2 ≤ wideAlpha m ^ 2 := by
  have hα : 0 ≤ wideAlpha m := (wideAlpha_pos hm).le
  unfold wideTriangular
  split_ifs with _ _
  · have hd := wideDiag_le_alpha hm (i : ℕ)
    have hdp : 0 ≤ wideDiagNat m (i : ℕ) := (wideDiag_pos hm (i : ℕ)).le
    nlinarith
  · have hc := wideC_le_one hm
    have hc0 : 0 ≤ wideC m := (wideC_pos hm).le
    have hd := wideDiag_le_alpha hm (i : ℕ)
    have hdp : 0 ≤ wideDiagNat m (i : ℕ) := (wideDiag_pos hm (i : ℕ)).le
    have hnn : 0 ≤ wideC m * wideDiagNat m (i : ℕ) := mul_nonneg hc0 hdp
    have hprod : wideC m * wideDiagNat m (i : ℕ) ≤ wideAlpha m := by
      calc
        wideC m * wideDiagNat m (i : ℕ) ≤ (1 : ℝ) * wideDiagNat m (i : ℕ) :=
          mul_le_mul_of_nonneg_right hc hdp
        _ ≤ (1 : ℝ) * wideAlpha m := mul_le_mul_of_nonneg_left hd (by norm_num)
        _ = wideAlpha m := one_mul _
    rw [show (-wideC m * wideDiagNat m (i : ℕ)) ^ 2 =
        (wideC m * wideDiagNat m (i : ℕ)) ^ 2 by ring]
    exact pow_le_pow_left₀ hnn hprod 2
  · nlinarith

lemma wide_leading_energy {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ)
    (hblock : ∀ i j : Fin (wideDim m),
      A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j)
    (j : Fin (wideDim m)) :
    residualSq A ∅ (j.castAdd (wideDim m * wideRepeats m)) ≤
      1 / (2 * (wideDim m : ℝ)) := by
  rw [residualSq_empty]
  have hsum : ∑ i, (A i (j.castAdd (wideDim m * wideRepeats m))) ^ 2 =
      ∑ i, (wideTriangular m i j) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hblock]
  rw [hsum]
  have hle : ∑ i, (wideTriangular m i j) ^ 2 ≤
      ∑ i : Fin (wideDim m), wideAlpha m ^ 2 :=
    Finset.sum_le_sum fun i _ => wideTriangular_entry_sq hm i j
  have hconst : ∑ i : Fin (wideDim m), wideAlpha m ^ 2 =
      (wideDim m : ℝ) * wideAlpha m ^ 2 := by
    simp [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk : (0 : ℝ) < wideDim m := by exact_mod_cast wideDim_pos hm
  have hαsq : wideAlpha m ^ 2 = 1 / (4 * (wideDim m : ℝ) ^ 2) := by
    unfold wideAlpha
    have hk0 : (wideDim m : ℝ) ≠ 0 := ne_of_gt hk
    field_simp [hk0]
    ring
  calc
    ∑ i, (wideTriangular m i j) ^ 2 ≤ (wideDim m : ℝ) * wideAlpha m ^ 2 := by
      rw [← hconst]
      exact hle
    _ = 1 / (4 * (wideDim m : ℝ)) := by
      rw [hαsq]
      field_simp
    _ ≤ 1 / (2 * (wideDim m : ℝ)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hk)
      nlinarith

lemma wide_filler_le {m : ℕ} (hm : 2 ≤ m) :
    (wideDim m : ℝ) / (wideRepeats m : ℝ) ≤ 1 / (2 * (wideDim m : ℝ)) := by
  have hrep : (wideRepeats m : ℝ) = 32 * (wideDim m : ℝ) ^ 3 := by
    unfold wideRepeats
    push_cast
    ring
  rw [hrep]
  have hk : (0 : ℝ) < wideDim m := by exact_mod_cast wideDim_pos hm
  have hk4 : (4 : ℝ) ≤ wideDim m := by
    have h4 : (4 : ℕ) ≤ wideDim m := by
      unfold wideDim
      have hmul := Nat.mul_le_mul hm hm
      omega
    exact_mod_cast h4
  rw [div_le_div_iff₀ (by positivity) (mul_pos (by norm_num) hk)]
  nlinarith

lemma wide_column_energy {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ)
    (hblock : ∀ i j : Fin (wideDim m),
      A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j)
    (hfill : ∀ j : Fin (wideDim m * wideRepeats m),
      vecEnergy (fun i => A i (j.natAdd (wideDim m))) ≤
        (wideDim m : ℝ) / (wideRepeats m : ℝ))
    (j : Fin (wideWidth m)) :
    residualSq A ∅ j ≤ 1 / (2 * (wideDim m : ℝ)) := by
  by_cases hj : (j : ℕ) < wideDim m
  · let q : Fin (wideDim m) := ⟨j, hj⟩
    have hjq : j = q.castAdd (wideDim m * wideRepeats m) := by
      ext
      simp [q]
    rw [hjq]
    exact wide_leading_energy hm A hblock q
  · have hge : wideDim m ≤ (j : ℕ) := Nat.le_of_not_lt hj
    let q : Fin (wideDim m * wideRepeats m) :=
      ⟨(j : ℕ) - wideDim m, by
        have hjlt : (j : ℕ) < wideWidth m := j.isLt
        unfold wideWidth at hjlt
        omega⟩
    have hjq : j = q.natAdd (wideDim m) := by
      ext
      simp [q, Nat.add_sub_of_le hge]
    have hres : residualSq A ∅ (q.natAdd (wideDim m)) =
        vecEnergy (fun i => A i (q.natAdd (wideDim m))) := by
      simp [residualSq_empty, vecEnergy]
    rw [hjq, hres]
    exact (hfill q).trans (wide_filler_le hm)

lemma wide_inner_abs_le {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ)
    (hblock : ∀ i j : Fin (wideDim m),
      A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j)
    (hfill : ∀ j : Fin (wideDim m * wideRepeats m),
      vecEnergy (fun i => A i (j.natAdd (wideDim m))) ≤
        (wideDim m : ℝ) / (wideRepeats m : ℝ))
    (i j : Fin (wideWidth m)) :
    |colInner A i j| ≤ 1 / (2 * (wideDim m : ℝ)) := by
  set B : ℝ := 1 / (2 * (wideDim m : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hE : ∀ t, residualSq A ∅ t ≤ B := wide_column_energy hm A hblock hfill
  have hsq : (colInner A i j) ^ 2 ≤ residualSq A ∅ i * residualSq A ∅ j := by
    simpa [colInner, residualSq_empty] using
      (Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin (wideDim m)))
        (fun r => A r i) (fun r => A r j))
  have hprod : residualSq A ∅ i * residualSq A ∅ j ≤ B * B := by
    have hi := hE i
    have hj := hE j
    have hni := residualSq_nonneg A ∅ i
    have hnj := residualSq_nonneg A ∅ j
    nlinarith
  have hsqB : (colInner A i j) ^ 2 ≤ B ^ 2 := by
    calc
      (colInner A i j) ^ 2 ≤ residualSq A ∅ i * residualSq A ∅ j := hsq
      _ ≤ B * B := hprod
      _ = B ^ 2 := by ring
  exact abs_le_of_sq_le_sq hsqB hB

lemma wide_frame_witness {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      ∃ x : Fin (widePrefix (wideWidth m) (wideDim m)).card → ℝ,
        OrthogonalRows A ∧
        ColumnIncoherent A (1 / (2 * (wideDim m : ℝ))) ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        vecEnergy (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x) = 1 ∧
        wideGrowthLower m ^ 2 ≤ vecEnergy x := by
  obtain ⟨A, hA, hblock, hset, hfill⟩ := wide_frame_pivots hm
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
    rw [hcast (Fin.cast hcard j), hblock]
    simp [x, y]
  refine ⟨A, x, hA, ?_, hset, ?_, ?_⟩
  · intro i j _
    exact wide_inner_abs_le hm A hblock hfill i j
  · rw [hmul]
    exact wideWitness_image_energy hm
  · rw [show vecEnergy x = vecEnergy y by
      simpa [x, y] using vecEnergy_finCast hcard y]
    exact wideWitness_energy_lower hm

theorem incoherent_no_joint_polynomial {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) {C : ℝ}
    (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        ColumnIncoherent A ρ ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x := by
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * ρ) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / Real.sqrt (2 * ρ))
  obtain ⟨m, hm, hpoly⟩ := exists_scale_beats_polynomial d hC N
  have hm2 : 2 ≤ m := (le_max_right N 2).trans hm
  have hNm : (N : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast le_trans (le_max_left N 2) hm
  have hbound : 1 / (2 * (wideDim m : ℝ)) ≤ ρ := by
    have hdim : (wideDim m : ℝ) = (m : ℝ) ^ 2 := wideDim_sq m
    have hroot : 1 / Real.sqrt (2 * ρ) < (m : ℝ) := lt_of_lt_of_le hN hNm
    have hself : (1 / Real.sqrt (2 * ρ)) * (1 / Real.sqrt (2 * ρ)) <
        (m : ℝ) * (m : ℝ) :=
      mul_self_lt_mul_self (by positivity) hroot
    have hsqsqrt : (Real.sqrt (2 * ρ)) ^ 2 = 2 * ρ := Real.sq_sqrt (by positivity)
    have hinv : (1 / Real.sqrt (2 * ρ)) * (1 / Real.sqrt (2 * ρ)) = 1 / (2 * ρ) := by
      rw [div_mul_div_comm, one_mul]
      congr 1
      rw [← pow_two, hsqsqrt]
    have hden : 1 / (2 * ρ) < (m : ℝ) ^ 2 := by
      rw [← hinv, pow_two]
      exact hself
    rw [hdim]
    have hpos : (0 : ℝ) < 2 * (m : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]
    have hposρ : (0 : ℝ) < 2 * ρ := by positivity
    rw [div_lt_iff₀ hposρ] at hden
    linarith
  obtain ⟨A, x, hA, hCinc, hset, hAx, hx⟩ := wide_frame_witness hm2
  refine ⟨wideDim m, wideWidth m, A, ?_⟩
  rw [hset]
  refine ⟨x, hA, ?_, ?_⟩
  · intro i j hij
    exact (hCinc i j hij).trans hbound
  · calc
      C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x)
          = C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) := by
            rw [hAx]
            ring
      _ < wideGrowthLower m ^ 2 := hpoly
      _ ≤ vecEnergy x := hx

end StructuredColumnSelection
