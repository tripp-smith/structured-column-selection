import StructuredColumnSelection.RowOrthoConstraints

/-! Finite CPQR back-substitution under an additional column ℓ¹ budget.
This hypothesis is not derived from row orthogonality. Milestone E stays open. -/
namespace StructuredColumnSelection
open Finset
open scoped Matrix

variable {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)

/-- The total absolute strict-upper mass in each column is at most one.
Allows branching and long edges; does not assume a bound on the inverse. -/
def gsUColumnBudget : Prop :=
  ∀ j : Fin k, ∑ l ∈ Iio j, |gsU A hA l j| ≤ 1

lemma gsS_abs_le_one_of_column_budget (hbudget : gsUColumnBudget A hA)
    (i j : Fin k) : |gsS A hA i j| ≤ 1 := by
  have aux : ∀ d : ℕ, ∀ i j : Fin k,
      (j : ℕ) - (i : ℕ) = d → |gsS A hA i j| ≤ 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hd
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
      · rw [gsS_recurrence A hA hlt, abs_neg]
        calc |∑ l ∈ Ico i j, gsS A hA i l * gsU A hA l j|
            ≤ ∑ l ∈ Ico i j, |gsS A hA i l * gsU A hA l j| :=
              abs_sum_le_sum_abs _ _
          _ ≤ ∑ l ∈ Ico i j, |gsU A hA l j| := by
            apply sum_le_sum
            intro l hl
            have hl' := mem_Ico.mp hl
            have hli : (i : ℕ) ≤ (l : ℕ) := Fin.le_def.mp hl'.1
            have hlj : (l : ℕ) < (j : ℕ) := Fin.lt_def.mp hl'.2
            have hsmall : (l : ℕ) - (i : ℕ) < d := by omega
            rw [abs_mul]
            exact (mul_le_mul_of_nonneg_right (ih _ hsmall i l rfl)
              (abs_nonneg _)).trans_eq (one_mul _)
          _ ≤ ∑ l ∈ Iio j, |gsU A hA l j| :=
            sum_le_sum_of_subset_of_nonneg
              (fun l hl => mem_Iio.mpr (mem_Ico.mp hl).2)
              (fun _ _ _ => abs_nonneg _)
          _ ≤ 1 := hbudget j
      · have hij : i = j := Fin.ext heq
        subst j
        rw [gsS_diag, abs_one]
      · rw [gsS_lower A hA hgt, abs_zero]
        exact zero_le_one
  exact aux _ i j rfl

lemma gsS_col_sq_sum_le_of_column_budget (hbudget : gsUColumnBudget A hA)
    (l : Fin k) :
    ∑ s : Fin k, (gsS A hA s l) ^ 2 ≤ ((l : ℕ) : ℝ) + 1 := by
  have hterm : ∀ s : Fin k,
      (gsS A hA s l) ^ 2 ≤
        if (s : ℕ) ≤ (l : ℕ) then (1 : ℝ) else 0 := by
    intro s
    rw [← sq_abs]
    by_cases h : (s : ℕ) ≤ (l : ℕ)
    · rw [if_pos h]
      exact pow_le_one₀ (abs_nonneg _)
        (gsS_abs_le_one_of_column_budget A hA hbudget s l)
    · rw [if_neg h, gsS_lower A hA (Nat.lt_of_not_ge h), abs_zero]
      simp
  calc ∑ s : Fin k, (gsS A hA s l) ^ 2
      ≤ ∑ s : Fin k, if (s : ℕ) ≤ (l : ℕ) then (1 : ℝ) else 0 :=
        sum_le_sum fun s _ => hterm s
    _ = ∑ s ∈ univ.filter fun s : Fin k => (s : ℕ) ≤ (l : ℕ), (1 : ℝ) := by
        simp
    _ = ((univ.filter fun s : Fin k => (s : ℕ) ≤ (l : ℕ)).card : ℝ) := by
        simp [sum_const, nsmul_eq_mul]
    _ = ((l : ℕ) : ℝ) + 1 := card_fin_val_le l

/-- Inverse-Frobenius proxy under a column budget on `U`.

This is a joint `poly(n,k)` bound on the **column-budget coefficient
pattern**, not a Path 1 theorem for every orthogonal-row matrix. General coupling without the budget remains open. Milestone E remains open. -/
theorem pivotGram_inv_trace_le_of_column_budget (hbudget : gsUColumnBudget A hA) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) := by
  have hkn := orthogonalRows_le A hA
  have hC : (0 : ℝ) ≤ (n : ℝ) - k + 1 := by
    have : (k : ℝ) ≤ n := Nat.cast_le.mpr hkn
    linarith
  rw [pivotGram_inv_trace]
  have hsum :
      ∑ l : Fin k, (((l : ℕ) : ℝ) + 1) = (k : ℝ) * (k + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun m => (m : ℝ) + 1) k]
    exact gauss_sum_succ k
  calc ∑ l : Fin k, (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l) ^ 2
      ≤ ∑ l : Fin k, ((n : ℝ) - k + 1) * (((l : ℕ) : ℝ) + 1) := by
        refine sum_le_sum fun l _ => ?_
        have hEnn : 0 ≤ ∑ s : Fin k, (gsS A hA s l) ^ 2 :=
          sum_nonneg fun _ _ => sq_nonneg _
        have hδ : (gsδ A hA l)⁻¹ ≤ (n : ℝ) - k + 1 :=
          (gsδ_inv_le A hA hkn l).trans (gsδ_ratio_le hkn l)
        have hE := gsS_col_sq_sum_le_of_column_budget A hA hbudget l
        calc (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l) ^ 2
            ≤ ((n : ℝ) - k + 1) * ∑ s : Fin k, (gsS A hA s l) ^ 2 :=
              mul_le_mul_of_nonneg_right hδ hEnn
          _ ≤ ((n : ℝ) - k + 1) * (((l : ℕ) : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hE hC
    _ = ((n : ℝ) - k + 1) * ∑ l : Fin k, (((l : ℕ) : ℝ) + 1) := by
        rw [← mul_sum]
    _ = ((n : ℝ) - k + 1) * ((k : ℝ) * (k + 1) / 2) := by rw [hsum]
    _ = ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) := by ring

end StructuredColumnSelection
