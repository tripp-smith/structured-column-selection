import StructuredColumnSelection.WideCPQRGrowth

/-! Column-energy escape for the wide CPQR family.

The outcome-2 frames leave every fixed leverage-ratio class. This file
does not prove a polynomial bound on that class. -/

namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

lemma wide_filler_count {m : ℕ} (hm : 2 ≤ m) :
    wideWidth m - wideDim m = 32 * wideDim m ^ 4 := by
  unfold wideWidth wideRepeats
  have hmul : wideDim m * (32 * wideDim m ^ 3) = 32 * wideDim m ^ 4 := by
    rw [Nat.mul_left_comm, Nat.mul_comm (wideDim m), ← Nat.pow_succ]
  rw [Nat.add_sub_cancel_left, hmul]

lemma wide_index_lt {m : ℕ} (hm : 2 ≤ m) : wideDim m < wideWidth m := by
  have hcount := wide_filler_count hm
  have hk : 0 < wideDim m := wideDim_pos hm
  exact Nat.sub_pos_iff_lt.mp (by rw [hcount]; exact Nat.mul_pos (by norm_num) (pow_pos hk _))

lemma wideAlpha_sq {m : ℕ} (hm : 2 ≤ m) :
    wideAlpha m ^ 2 = 1 / (4 * (wideDim m : ℝ) ^ 2) := by
  unfold wideAlpha
  have hk : (wideDim m : ℝ) ≠ 0 := by exact_mod_cast (wideDim_pos hm).ne'
  field_simp [hk]
  ring

lemma wide_first_column_energy {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ)
    (hblock : ∀ i j : Fin (wideDim m),
      A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) :
    let j0 : Fin (wideWidth m) := ⟨0, Nat.zero_lt_of_lt (wide_index_lt hm)⟩
    residualSq A ∅ j0 = wideAlpha m ^ 2 := by
  intro j0
  let z : Fin (wideDim m) := ⟨0, wideDim_pos hm⟩
  have hidx : j0 = z.castAdd (wideDim m * wideRepeats m) := by
    apply Fin.ext
    show (j0 : ℕ) = (z : ℕ)
    rfl
  rw [residualSq_empty, Finset.sum_eq_single z]
  · have hz : A z j0 = wideAlpha m := by
      rw [hidx, hblock, wideTriangular, if_pos rfl, wideDiagNat]
      simp [z, pow_zero]
    rw [hz]
  · intro i _ hi
    have hlt : ¬ (i : ℕ) < (z : ℕ) := by simpa [z] using Nat.not_lt_zero (i : ℕ)
    rw [hidx, hblock, wideTriangular, if_neg hi, if_neg hlt]
    simp
  · intro h
    exact (h (mem_univ _)).elim

/-- For every nonnegative `τ`, some outcome-2 frame has two column energies
with ratio greater than `τ`. On that frame the ratio is also greater than `8 m²`. -/
theorem wide_leverage_escape {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ m : ℕ, 2 ≤ m ∧
      ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
        OrthogonalRows A ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        ∃ jMin jMax : Fin (wideWidth m),
          τ * residualSq A ∅ jMin < residualSq A ∅ jMax ∧
          (8 * (wideDim m : ℝ)) * residualSq A ∅ jMin < residualSq A ∅ jMax := by
  obtain ⟨N, hN⟩ := exists_nat_gt (τ / 8)
  let m := max N 2
  have hm : 2 ≤ m := le_max_right _ _
  have hbig : τ < 8 * (wideDim m : ℝ) := by
    have hN' : τ / 8 < (N : ℝ) := hN
    have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left N 2
    have hdim : (wideDim m : ℝ) = (m : ℝ) ^ 2 := by
      unfold wideDim
      push_cast
      ring
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    calc
      τ = 8 * (τ / 8) := by ring
      _ < 8 * (N : ℝ) := by gcongr
      _ ≤ 8 * (m : ℝ) := by gcongr
      _ ≤ 8 * (wideDim m : ℝ) := by rw [hdim]; gcongr
  obtain ⟨A, _x, hA, hblock, hset, _himg, _henergy⟩ := wide_adverse_family hm
  let j0 : Fin (wideWidth m) := ⟨0, Nat.zero_lt_of_lt (wide_index_lt hm)⟩
  let e : Fin (wideWidth m) → ℝ := fun j => residualSq A ∅ j
  have he0 : e j0 = 1 / (4 * (wideDim m : ℝ) ^ 2) := by
    rw [show e j0 = wideAlpha m ^ 2 by
      simpa [e, j0] using wide_first_column_energy hm A hblock]
    exact wideAlpha_sq hm
  have hpos : 0 < e j0 := by
    rw [he0]
    exact div_pos one_pos (mul_pos (by norm_num) (pow_pos (by exact_mod_cast wideDim_pos hm) _))
  let lead := widePrefix (wideWidth m) (wideDim m)
  have hj0 : j0 ∈ lead := by
    change j0 ∈ (univ : Finset (Fin (wideWidth m))).filter
      fun j : Fin (wideWidth m) => (j : ℕ) < wideDim m
    rw [mem_filter]
    exact ⟨mem_univ _, by simpa [j0] using wideDim_pos hm⟩
  have hnn : ∀ j, 0 ≤ e j := fun j => residualSq_nonneg A ∅ j
  have hlead : e j0 ≤ ∑ j ∈ lead, e j := by
    rw [← Finset.add_sum_erase lead e hj0]
    have : 0 ≤ ∑ j ∈ lead.erase j0, e j := Finset.sum_nonneg fun _ _ => hnn _
    linarith
  have hsum : ∑ j, e j = (wideDim m : ℝ) := by simpa [e] using leverageSum A hA
  have hsplit :
      ∑ j ∈ univ \ lead, e j + ∑ j ∈ lead, e j = (wideDim m : ℝ) := by
    rw [← hsum]
    exact Finset.sum_sdiff (subset_univ lead)
  have hcompEq : ∑ j ∈ univ \ lead, e j = (wideDim m : ℝ) - ∑ j ∈ lead, e j :=
    (eq_sub_of_add_eq hsplit)
  have hcomp : ∑ j ∈ univ \ lead, e j ≤ (wideDim m : ℝ) - e j0 := by
    rw [hcompEq]
    exact sub_le_sub_left hlead _
  have hfill : (univ \ lead).Nonempty := by
    refine ⟨⟨wideDim m, wide_index_lt hm⟩, ?_⟩
    change (⟨wideDim m, wide_index_lt hm⟩ : Fin (wideWidth m)) ∈
      (univ : Finset (Fin (wideWidth m))) \
        (univ : Finset (Fin (wideWidth m))).filter
          fun j : Fin (wideWidth m) => (j : ℕ) < wideDim m
    rw [mem_sdiff, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    intro hmem
    have hlt : (wideDim m : ℕ) < wideDim m := by simpa [Fin.val_mk] using hmem.2
    exact lt_irrefl _ hlt
  obtain ⟨jMin, _hjMin, hmin⟩ := Finset.exists_min_image (univ \ lead) e hfill
  have hcard : ((univ \ lead).card : ℝ) = 32 * (wideDim m : ℝ) ^ 4 := by
    rw [Finset.card_sdiff_of_subset (subset_univ lead), card_univ, Fintype.card_fin,
      widePrefix_card (Nat.le_add_right _ _), wide_filler_count hm]
    norm_cast
  have havg : e jMin * (32 * (wideDim m : ℝ) ^ 4) ≤ (wideDim m : ℝ) - e j0 := by
    have hge : ∀ j ∈ univ \ lead, e jMin ≤ e j := fun j hj => hmin j hj
    have hsumge := Finset.sum_le_sum hge
    have : e jMin * ((univ \ lead).card : ℝ) ≤ ∑ j ∈ univ \ lead, e j := by
      simpa [sum_const, nsmul_eq_mul, mul_comm] using hsumge
    rw [hcard] at this
    exact this.trans hcomp
  have hbelow : (wideDim m : ℝ) - e j0 < (wideDim m : ℝ) := by linarith
  have hscale : e j0 / (8 * (wideDim m : ℝ)) = 1 / (32 * (wideDim m : ℝ) ^ 3) := by
    rw [he0, div_div]
    congr 1
    ring
  have havgBound : (wideDim m : ℝ) / (32 * (wideDim m : ℝ) ^ 4) =
      1 / (32 * (wideDim m : ℝ) ^ 3) := by
    have hk0 : (0 : ℝ) < (wideDim m : ℝ) := by exact_mod_cast wideDim_pos hm
    set k : ℝ := (wideDim m : ℝ)
    have hk : 0 < k := by simpa [k] using hk0
    have hpow : k ^ 4 = k * k ^ 3 := by rw [pow_succ, mul_comm]
    calc
      k / (32 * k ^ 4) = k / (32 * (k * k ^ 3)) := by rw [hpow]
      _ = k / (k * (32 * k ^ 3)) := by ring
      _ = (k / k) / (32 * k ^ 3) := by rw [← div_div]
      _ = 1 / (32 * k ^ 3) := by rw [div_self hk.ne']
  have hratio : (8 * (wideDim m : ℝ)) * e jMin < e j0 := by
    by_cases hzero : e jMin = 0
    · rw [hzero, mul_zero]
      exact hpos
    · have hposmin : 0 < e jMin := lt_of_le_of_ne (hnn jMin) (Ne.symm hzero)
      have hdiv : e jMin ≤ ((wideDim m : ℝ) - e j0) / (32 * (wideDim m : ℝ) ^ 4) := by
        have hden : (0 : ℝ) < 32 * (wideDim m : ℝ) ^ 4 :=
          mul_pos (by norm_num) (pow_pos (by exact_mod_cast wideDim_pos hm) _)
        rw [le_div_iff₀ hden]
        exact havg
      have hden : (0 : ℝ) < 32 * (wideDim m : ℝ) ^ 4 :=
        mul_pos (by norm_num) (pow_pos (by exact_mod_cast wideDim_pos hm) _)
      have hstrict :
          ((wideDim m : ℝ) - e j0) / (32 * (wideDim m : ℝ) ^ 4) <
            (wideDim m : ℝ) / (32 * (wideDim m : ℝ) ^ 4) :=
        div_lt_div_of_pos_right hbelow hden
      have : e jMin < e j0 / (8 * (wideDim m : ℝ)) :=
        hdiv.trans_lt (hstrict.trans_eq (havgBound.trans hscale.symm))
      have h8 : (0 : ℝ) < 8 * (wideDim m : ℝ) :=
        mul_pos (by norm_num) (by exact_mod_cast wideDim_pos hm)
      rw [mul_comm]
      rwa [lt_div_iff₀ h8] at this
  refine ⟨m, hm, A, hA, hset, jMin, j0, ?_, hratio⟩
  · by_cases hzero : e jMin = 0
    · change τ * e jMin < e j0
      rw [hzero, mul_zero]
      exact hpos
    · have hposmin : 0 < e jMin := lt_of_le_of_ne (hnn jMin) (Ne.symm hzero)
      exact (mul_lt_mul_of_pos_right hbig hposmin).trans hratio

end StructuredColumnSelection
