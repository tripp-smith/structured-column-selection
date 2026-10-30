import StructuredColumnSelection.WideCPQR
import StructuredColumnSelection.WideCPQRParameters

/-! Instantiation of the prescribed triangular block as an actual CPQR frame. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

lemma tailEnergy_step {k : ℕ} (p : Fin k) (x : Fin k → ℝ) :
    tailEnergy p x = x p ^ 2 + tailEnergy ((p : ℕ)+1) x := by
  unfold tailEnergy
  calc
    _ = ∑ i : Fin k, ((if i=p then x p ^ 2 else 0) +
        (if (p : ℕ)+1 ≤ (i : ℕ) then x i ^ 2 else 0)) := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i=p
      · subst i; simp
      · have hne : (i : ℕ) ≠ (p : ℕ) := fun h => hi (Fin.ext h)
        by_cases hlt : (i : ℕ) < (p : ℕ)
        · simp [hi,show ¬ (p : ℕ) ≤ (i : ℕ) by omega,
            show ¬ (p : ℕ)+1 ≤ (i : ℕ) by omega]
        · simp [hi,show (p : ℕ) ≤ (i : ℕ) by omega,
            show (p : ℕ)+1 ≤ (i : ℕ) by omega]
    _ = _ := by simp [sum_add_distrib]

lemma tailEnergy_le_energy {k : ℕ} (t : ℕ) (x : Fin k → ℝ) :
    tailEnergy t x ≤ vecEnergy x := by
  apply sum_le_sum
  intro i _
  split_ifs <;> simp [sq_nonneg]

lemma wideTriangular_entry_sq_le {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (wideDim m)) : wideTriangular m i j ^ 2 ≤ wideAlpha m ^ 2 := by
  have hd := wideDiag_pos hm i
  have hda := wideDiag_le_alpha hm i
  have hc := wideC_pos hm
  have hc1 := wideC_le_one hm
  have ha := wideAlpha_pos hm
  have hd2 : wideDiagNat m i ^ 2 ≤ wideAlpha m ^ 2 := by nlinarith
  unfold wideTriangular
  split_ifs with hij hlt
  · exact hd2
  · have hc2 : wideC m ^ 2 ≤ 1 := by nlinarith
    calc
      (-wideC m * wideDiagNat m i)^2 = wideC m ^ 2 * wideDiagNat m i ^ 2 := by ring
      _ ≤ 1 * wideDiagNat m i ^ 2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ ≤ _ := by simpa using hd2
  · nlinarith [sq_nonneg (wideAlpha m)]

lemma wideTriangular_frob_le {m : ℕ} (hm : 2 ≤ m) :
    frobEnergy (wideTriangular m) ≤ 1 := by
  have hk := wideDim_pos hm
  have hkR : (0 : ℝ) < wideDim m := by exact_mod_cast hk
  calc
    frobEnergy (wideTriangular m)
        ≤ ∑ _i : Fin (wideDim m), ∑ _j : Fin (wideDim m), wideAlpha m ^ 2 :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => wideTriangular_entry_sq_le hm i j
    _ = (1 : ℝ)/4 := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, wideAlpha]
      field_simp [ne_of_gt hkR]
      ring
    _ ≤ 1 := by norm_num

lemma wideTriangular_tail_step {m : ℕ} (p j : Fin (wideDim m))
    (hpj : (p : ℕ) < (j : ℕ)) :
    tailEnergy p ((wideTriangular m).col j) =
      wideC m ^ 2 * wideDiagNat m p ^ 2 +
        tailEnergy ((p : ℕ)+1) ((wideTriangular m).col j) := by
  rw [tailEnergy_step]
  have hne : p ≠ j := fun h => by subst j; omega
  simp only [Matrix.col_apply, wideTriangular, if_neg hne, if_pos hpj]
  ring

lemma wideTriangular_tail_diag (m : ℕ) (j : Fin (wideDim m)) :
    tailEnergy j ((wideTriangular m).col j) = wideDiagNat m j ^ 2 := by
  simpa only [Fin.castLE_refl, wideTriangular_diag] using
    leading_tail_diag (Nat.le_refl (wideDim m)) (wideTriangular m)
      (fun _ _ h => wideTriangular_upper h) j

lemma wideTriangular_tail_le {m : ℕ} (hm : 2 ≤ m) (j : Fin (wideDim m))
    (t : ℕ) (ht : t ≤ (j : ℕ)) :
    tailEnergy t ((wideTriangular m).col j) ≤ wideDiagNat m t ^ 2 := by
  have hall : ∀ r : ℕ, ∀ t : ℕ, t+r=(j : ℕ) →
      tailEnergy t ((wideTriangular m).col j) ≤ wideDiagNat m t ^ 2 := by
    intro r
    induction r with
    | zero =>
      intro t h
      have heq : t=(j : ℕ) := by omega
      subst t
      exact (wideTriangular_tail_diag m j).le
    | succ r ih =>
      intro t h
      let p : Fin (wideDim m) := ⟨t,by omega⟩
      have hpj : (p : ℕ) < (j : ℕ) := by dsimp [p]; omega
      have hnext := ih (t+1) (by omega)
      have hstep := wideTriangular_tail_step p j hpj
      have hc := wide_coupling_budget hm
      have hd := wideDiag_pos hm t
      have hrec := wideDiag_succ m t
      change tailEnergy t _ = _ at hstep
      calc
        tailEnergy t ((wideTriangular m).col j)
            ≤ wideC m ^ 2 * wideDiagNat m t ^ 2 + wideDiagNat m (t+1)^2 := by
          dsimp [p] at hstep
          linarith
        _ = (wideC m ^ 2 + wideEps m ^ 2) * wideDiagNat m t ^ 2 := by rw [hrec]; ring
        _ ≤ wideDiagNat m t ^ 2 := by nlinarith [sq_pos_of_pos hd]
  exact hall ((j : ℕ)-t) t (by omega)

lemma wideTriangular_tail_lt {m : ℕ} (hm : 2 ≤ m)
    (p j : Fin (wideDim m)) (hpj : (p : ℕ) < (j : ℕ)) :
    tailEnergy p ((wideTriangular m).col j) < wideDiagNat m p ^ 2 := by
  rw [wideTriangular_tail_step p j hpj]
  have hn := wideTriangular_tail_le hm j ((p : ℕ)+1) (by omega)
  have hc := wide_coupling_budget hm
  have hd := wideDiag_pos hm p
  rw [wideDiag_succ] at hn
  nlinarith [sq_pos_of_pos hd]

def wideRepeats (m : ℕ) : ℕ := 32 * wideDim m ^ 3
abbrev wideWidth (m : ℕ) : ℕ := wideDim m + wideDim m * wideRepeats m

lemma wide_filler_lt_diag {m : ℕ} (hm : 2 ≤ m) (p : Fin (wideDim m)) :
    (wideDim m : ℝ) / (wideRepeats m : ℝ) < wideDiagNat m p ^ 2 := by
  have hk := wideDim_pos hm
  have hkR : (0 : ℝ) < wideDim m := by exact_mod_cast hk
  have hd := wideDiag_half_lower hm p.isLt
  have hhalf : 0 < wideAlpha m / 2 := by
    linarith [wideAlpha_pos hm]
  have hsq : (wideAlpha m / 2) ^ 2 < wideDiagNat m p ^ 2 :=
    sq_lt_sq.mpr (by
      rw [abs_of_pos hhalf, abs_of_pos (wideDiag_pos hm p)]
      exact hd)
  have hrep : (wideRepeats m : ℝ) = 32 * (wideDim m : ℝ) ^ 3 := by
    unfold wideRepeats
    push_cast
    ring
  have hsmall : (wideDim m : ℝ) / (wideRepeats m : ℝ) < (wideAlpha m / 2) ^ 2 := by
    rw [hrep, wideAlpha]
    have hk0 : (wideDim m : ℝ) ≠ 0 := ne_of_gt hkR
    field_simp [hk0]
    nlinarith [sq_pos_of_pos hkR]
  exact hsmall.trans hsq

/-- An actual all-parameter orthogonal-row family with its literal CPQR prefix. -/
theorem wide_frame_pivots {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin (wideDim m),
        A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) ∧
      cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
      (∀ j : Fin (wideDim m * wideRepeats m),
        vecEnergy (fun i => A i (j.natAdd (wideDim m))) ≤
          (wideDim m : ℝ) / (wideRepeats m : ℝ)) ∧
      ∃ j1 j2 : Fin (wideWidth m),
        j1 ≠ j2 ∧ (∀ i, A i j1 = A i j2) ∧
          0 < vecEnergy (fun i => A i j1) := by
  have ht : 0 < wideRepeats m := by
    unfold wideRepeats
    exact Nat.mul_pos (by norm_num) (pow_pos (wideDim_pos hm) _)
  have ht2 : 2 ≤ wideRepeats m := by
    have hpow : 1 ≤ wideDim m ^ 3 := Nat.one_le_pow 3 _ (wideDim_pos hm)
    have hmul : 32 ≤ 32 * wideDim m ^ 3 := Nat.mul_le_mul_left 32 hpow
    have h2 : 2 ≤ 32 := by norm_num
    exact h2.trans (by simpa [wideRepeats] using hmul)
  obtain ⟨A, hA, hR, hC, hDup⟩ := wide_completion_with_repeat
    (wideTriangular m) (wideTriangular_frob_le hm) (wideRepeats m) ht2
    (by
      unfold wideDim
      have hmul := Nat.mul_le_mul hm hm
      omega)
  have hkn : wideDim m ≤ wideWidth m := Nat.le_add_right _ _
  have hcast (j : Fin (wideDim m)) :
      Fin.castLE hkn j = j.castAdd (wideDim m * wideRepeats m) := by rfl
  have hupper : ∀ i j : Fin (wideDim m), (j : ℕ) < (i : ℕ) →
      A i (Fin.castLE hkn j) = 0 := by
    intro i j h
    rw [hcast,hR]
    exact wideTriangular_upper h
  have hdiag : ∀ i : Fin (wideDim m), A i (Fin.castLE hkn i) ≠ 0 := by
    intro i
    rw [hcast,hR,wideTriangular_diag]
    exact (wideDiag_pos hm i).ne'
  have htail : ∀ p : Fin (wideDim m), ∀ j : Fin (wideWidth m),
      (p : ℕ) < (j : ℕ) → tailEnergy p (A.col j) < A p (Fin.castLE hkn p)^2 := by
    intro p j hpj
    rw [hcast, hR, wideTriangular_diag]
    by_cases hj : (j : ℕ) < wideDim m
    · let q : Fin (wideDim m) := ⟨j, hj⟩
      have hjq : j = q.castAdd (wideDim m * wideRepeats m) := by
        ext
        simp [q]
      have hpq : (p : ℕ) < (q : ℕ) := by
        have : (j : ℕ) = (q : ℕ) := by simp [hjq]
        omega
      have hcol : A.col j = (wideTriangular m).col q := by
        ext i
        rw [hjq]
        exact hR i q
      rw [hcol]
      exact wideTriangular_tail_lt hm p q hpq
    · have hge : wideDim m ≤ (j : ℕ) := Nat.le_of_not_lt hj
      let q : Fin (wideDim m * wideRepeats m) :=
        ⟨(j : ℕ) - wideDim m, by
          have hjlt : (j : ℕ) < wideWidth m := j.isLt
          unfold wideWidth at hjlt
          omega⟩
      have hjq : j = q.natAdd (wideDim m) := by
        ext
        simp [q, Nat.add_sub_of_le hge]
      rw [hjq]
      exact (tailEnergy_le_energy p _).trans_lt
        ((hC q).trans_lt (wide_filler_lt_diag hm p))
  refine ⟨A, hA, hR, ?_, hC, hDup⟩
  exact triangular_prefix_pivots hkn A hupper hdiag htail (wideDim m) (Nat.le_refl _)

end StructuredColumnSelection
