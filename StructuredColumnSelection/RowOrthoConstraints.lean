import StructuredColumnSelection.TriangularBound

/-!
# Row-orthonormality of the implicit CPQR factor (Milestone E, Path 1 partial)

The Businger–Golub bound `|S i j| ≤ 2^{j-i-1}` in `TriangularBound.lean` uses
only unit rows of the triangular factor (`|U| ≤ 1` from greedy maximality).
That estimate is exponentially loose in `k`. This module records the extra
algebra coming from **row-orthonormality of the implicit thin QR factor** of
an orthogonal-row matrix: after expanding every column of `A` in the CPQR
Gram–Schmidt basis, the coordinate matrix `R` satisfies `R Rᵀ = I`, not
merely that each selected diagonal is positive.

Proved here, with no placeholders:

* `gsR * gsRᵀ = 1`.
* Weighted row energy of `U`: `δ_s ∑_t U_s t² ≤ 1`, hence `∑_t U_s t² ≤ 1/δ_s`.
* Weighted column energy of `U`: `∑_s δ_s U_s t² ≤ 1`, hence the unweighted
  column energy `∑_s U_s t² ≤ n-k+1`.
* Nearest-neighbor (bidiagonal `U`) back-substitution does not amplify:
  `|S i j| ≤ 1`, and the inverse-Frobenius proxy is at most
  `k(k+1)/2 · (n-k+1)` — a joint `poly(n,k)` bound **on that coefficient
  pattern**, not on every orthogonal-row matrix.

Non-claims (intentional):

* This is **not** a joint `poly(n,k)` inverse-norm / inverse-Frobenius bound
  for every orthogonal-row matrix. Multi-neighbor coupling in `U` can still
  feed the Businger–Golub `2^{j-i}` recurrence; whether the `n-k+1` column
  budget forbids that growth is open.
* Milestone E remains **OPEN**. This module does not close Path 1.
* No CSSP / Milestone F statement.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

lemma col_dot_eq_transpose_mulVec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) (v : Fin k → ℝ) :
    (A.col j ⬝ᵥ v) = (Aᵀ *ᵥ v) j := by
  rw [dotProduct_eq, mulVec_eq_sum_transpose]
  simp only [show A.col j = fun i => A i j from rfl]

lemma gauss_sum_succ (m : ℕ) :
    ∑ t ∈ range m, ((t : ℝ) + 1) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

lemma card_fin_val_le {k : ℕ} (l : Fin k) :
    ((univ.filter fun s : Fin k => (s : ℕ) ≤ (l : ℕ)).card : ℝ) =
      (l : ℕ) + 1 := by
  have hcard :
      (univ.filter fun s : Fin k => (s : ℕ) ≤ (l : ℕ)).card = (l : ℕ) + 1 := by
    rw [← card_range ((l : ℕ) + 1)]
    refine card_bij (fun s _ => (s : ℕ)) ?_ ?_ ?_
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs
      exact mem_range.mpr (Nat.lt_succ_of_le hs)
    · intro s _ t _ h
      exact Fin.ext h
    · intro m hm
      have hm' : m < (l : ℕ) + 1 := mem_range.mp hm
      refine ⟨⟨m, lt_of_lt_of_le hm' (Nat.succ_le_of_lt l.isLt)⟩, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and]
      exact Nat.le_of_lt_succ hm'
  rw [hcard]
  norm_cast

section RowOrthoQR

variable {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)

include hA

/-! ### Implicit thin QR factor -/

/-- Coordinates of the columns of `A` in the CPQR Gram–Schmidt basis
`w_s / ‖w_s‖`. Rows of this `k × n` factor are orthonormal. -/
noncomputable def gsR : Matrix (Fin k) (Fin n) ℝ :=
  fun s j => (A.col j ⬝ᵥ gsW A hA s) * (Real.sqrt (gsδ A hA s))⁻¹

lemma gsR_apply (s : Fin k) (j : Fin n) :
    gsR A hA s j = (A.col j ⬝ᵥ gsW A hA s) * (Real.sqrt (gsδ A hA s))⁻¹ :=
  rfl

lemma gsδ_sqrt_pos (s : Fin k) : 0 < Real.sqrt (gsδ A hA s) :=
  Real.sqrt_pos.mpr (gsδ_pos A hA s.isLt)

lemma gsδ_sqrt_ne_zero (s : Fin k) : Real.sqrt (gsδ A hA s) ≠ 0 :=
  (gsδ_sqrt_pos A hA s).ne'

lemma gsδ_sqrt_sq (s : Fin k) :
    Real.sqrt (gsδ A hA s) ^ 2 = gsδ A hA s :=
  Real.sq_sqrt (le_of_lt (gsδ_pos A hA s.isLt))

lemma inv_sqrt_gsδ (s : Fin k) :
    (Real.sqrt (gsδ A hA s))⁻¹ =
      (gsδ A hA s)⁻¹ * Real.sqrt (gsδ A hA s) := by
  have hsq := gsδ_sqrt_sq A hA s
  have hne := gsδ_sqrt_ne_zero A hA s
  have hpow : ((Real.sqrt (gsδ A hA s)) ^ 2)⁻¹ * Real.sqrt (gsδ A hA s) =
      (Real.sqrt (gsδ A hA s))⁻¹ := by
    rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  calc (Real.sqrt (gsδ A hA s))⁻¹
      = ((Real.sqrt (gsδ A hA s)) ^ 2)⁻¹ * Real.sqrt (gsδ A hA s) := hpow.symm
    _ = (gsδ A hA s)⁻¹ * Real.sqrt (gsδ A hA s) := by rw [hsq]

lemma gsδ_mul_inv_sqrt (s : Fin k) :
    gsδ A hA s * (Real.sqrt (gsδ A hA s))⁻¹ = Real.sqrt (gsδ A hA s) := by
  rw [inv_sqrt_gsδ, ← mul_assoc, mul_inv_cancel₀ (gsδ_ne_zero A hA s.isLt),
    one_mul]

/-- Parseval pairing: summing column inner products against two Gram–Schmidt
directions recovers the directions' inner product, via `AAᵀ = I`. -/
lemma sum_col_dot_gsW (s t : Fin k) :
    ∑ j : Fin n, (A.col j ⬝ᵥ gsW A hA s) * (A.col j ⬝ᵥ gsW A hA t) =
      gsW A hA s ⬝ᵥ gsW A hA t := by
  have hpair :
      ∑ j : Fin n, (A.col j ⬝ᵥ gsW A hA s) * (A.col j ⬝ᵥ gsW A hA t) =
        (Aᵀ *ᵥ gsW A hA s) ⬝ᵥ (Aᵀ *ᵥ gsW A hA t) := by
    have hsj : ∀ j, (A.col j ⬝ᵥ gsW A hA s) = (Aᵀ *ᵥ gsW A hA s) j :=
      fun j => col_dot_eq_transpose_mulVec A j _
    have htj : ∀ j, (A.col j ⬝ᵥ gsW A hA t) = (Aᵀ *ᵥ gsW A hA t) j :=
      fun j => col_dot_eq_transpose_mulVec A j _
    simp only [hsj, htj, dotProduct_eq]
  rw [hpair, transpose_mulVec_dot, ← mulVec_mul_eq]
  have hAA : A * Aᵀ = (1 : Matrix (Fin k) (Fin k) ℝ) := hA
  rw [hAA, one_mulVec_eq]

/-- The implicit CPQR factor is row-orthonormal: `R Rᵀ = I`.

This is strictly stronger than unit rows of the triangular `U`, and is the
extra constraint used below. It is not an inverse-norm bound. -/
theorem gsR_mul_transpose : gsR A hA * (gsR A hA)ᵀ = 1 := by
  apply Matrix.ext
  intro s t
  have hmul :
      (gsR A hA * (gsR A hA)ᵀ) s t =
        ∑ j : Fin n, gsR A hA s j * gsR A hA t j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hfact :
      ∑ j : Fin n, gsR A hA s j * gsR A hA t j =
        (Real.sqrt (gsδ A hA s))⁻¹ * (Real.sqrt (gsδ A hA t))⁻¹ *
          ∑ j : Fin n, (A.col j ⬝ᵥ gsW A hA s) * (A.col j ⬝ᵥ gsW A hA t) := by
    simp only [gsR_apply]
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hmul, hfact, sum_col_dot_gsW]
  rcases eq_or_ne s t with hst | hst
  · subst hst
    have hone : (1 : Matrix (Fin k) (Fin k) ℝ) s s = 1 := Matrix.one_apply_eq s
    rw [gsW_sq A hA s.isLt, hone]
    have hsq := gsδ_sqrt_sq A hA s
    calc (Real.sqrt (gsδ A hA s))⁻¹ * (Real.sqrt (gsδ A hA s))⁻¹ * gsδ A hA s
        = ((Real.sqrt (gsδ A hA s)) ^ 2)⁻¹ * gsδ A hA s := by
          rw [pow_two, mul_inv]
      _ = (gsδ A hA s)⁻¹ * gsδ A hA s := by rw [hsq]
      _ = 1 := inv_mul_cancel₀ (gsδ_ne_zero A hA s.isLt)
  · have h0 : (1 : Matrix (Fin k) (Fin k) ℝ) s t = 0 := Matrix.one_apply_ne hst
    rw [gsW_orth' A hA hst, h0, mul_zero]

/-- Each row of `R` has Euclidean energy `1`. -/
lemma gsR_row_sq_sum (s : Fin k) :
    ∑ j : Fin n, (gsR A hA s j) ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M s s)
    (gsR_mul_transpose A hA)
  have hmul :
      (gsR A hA * (gsR A hA)ᵀ) s s =
        ∑ j : Fin n, gsR A hA s j * gsR A hA s j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  have hone : (1 : Matrix (Fin k) (Fin k) ℝ) s s = 1 := Matrix.one_apply_eq s
  rw [hmul, hone] at h
  refine Eq.trans (sum_congr rfl fun j _ => pow_two _) h

/-! ### Pivot columns inside `R` -/

lemma cpqrChosen_injective {s t : Fin k}
    (h : cpqrChosen A hA s s.isLt = cpqrChosen A hA t t.isLt) : s = t := by
  wlog hst : (s : ℕ) ≤ (t : ℕ) generalizing s t
  · exact (this h.symm (le_of_not_ge hst)).symm
  rcases eq_or_lt_of_le hst with heq | hlt
  · exact Fin.ext heq
  · have hmem : cpqrChosen A hA s s.isLt ∈ cpqrIterate A t :=
      cpqrIterate_mono A hA (Nat.succ_le_of_lt hlt) (le_of_lt t.isLt)
        (pivot_mem_iterate_succ A hA s.isLt)
    exact absurd (h ▸ hmem) (cpqrChosen_spec A hA t.isLt).1

/-- On the pivot columns, `R_s,t = U_s t √δ_s`. -/
lemma gsR_pivot (s t : Fin k) :
    gsR A hA s (cpqrChosen A hA t t.isLt) =
      gsU A hA s t * Real.sqrt (gsδ A hA s) := by
  rw [gsR_apply, show A.col (cpqrChosen A hA t t.isLt) = pivotVec A hA t from rfl]
  by_cases hst : (s : ℕ) < (t : ℕ)
  · rw [gsU_apply_of_lt A hA hst, inv_sqrt_gsδ A hA s]
    ring
  · by_cases hseq : s = t
    · subst hseq
      rw [gsU_apply_diag, one_mul, pivotVec_dot_gsW A hA s.isLt]
      exact gsδ_mul_inv_sqrt A hA s
    · have hgt : (t : ℕ) < (s : ℕ) := by
        rcases lt_or_gt_of_ne (fun hc => hseq (Fin.ext hc)) with h1 | h2
        · exact absurd h1 hst
        · exact h2
      rw [gsU_apply_of_gt A hA hgt, zero_mul]
      have hdot : (pivotVec A hA t ⬝ᵥ gsW A hA s) = 0 := by
        have hx : pivotVec A hA t =
            ∑ u : Fin k, gsU A hA u t • gsW A hA u :=
          pivotVec_eq_sum_gsU A hA t
        rw [hx, sum_dotProduct]
        refine sum_eq_zero fun u _ => ?_
        rw [smul_dotProduct, smul_eq_mul]
        by_cases hu : u = s
        · subst hu
          rw [gsU_apply_of_gt A hA hgt, zero_mul]
        · rw [gsW_orth' A hA hu, mul_zero]
      rw [hdot, zero_mul]

/-- Pivot columns are a subset of all columns, so each row of the selected
triangular block has energy at most `1`. -/
lemma gsR_row_pivot_sq_sum_le (s : Fin k) :
    ∑ t : Fin k, (gsR A hA s (cpqrChosen A hA t t.isLt)) ^ 2 ≤ 1 := by
  have hrow := gsR_row_sq_sum A hA s
  have himg :
      ∑ t : Fin k, (gsR A hA s (cpqrChosen A hA t t.isLt)) ^ 2 =
        ∑ j ∈ univ.image fun t : Fin k => cpqrChosen A hA t t.isLt,
          (gsR A hA s j) ^ 2 := by
    rw [sum_image]
    intro t _ u _ heq
    exact cpqrChosen_injective A hA heq
  rw [himg]
  have hsub :=
    sum_le_sum_of_subset_of_nonneg
      (s := univ.image fun t : Fin k => cpqrChosen A hA t t.isLt)
      (f := fun j : Fin n => (gsR A hA s j) ^ 2)
      (subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  exact hsub.trans_eq hrow

/-- Row-orthonormality on the selected block: `δ_s ∑_t U_s t² ≤ 1`. -/
lemma gsU_row_energy_mul_gsδ_le (s : Fin k) :
    gsδ A hA s * ∑ t : Fin k, (gsU A hA s t) ^ 2 ≤ 1 := by
  have h := gsR_row_pivot_sq_sum_le A hA s
  have heq :
      ∑ t : Fin k, (gsR A hA s (cpqrChosen A hA t t.isLt)) ^ 2 =
        gsδ A hA s * ∑ t : Fin k, (gsU A hA s t) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [gsR_pivot, mul_pow, gsδ_sqrt_sq, mul_comm]
  rw [← heq]
  exact h

/-- Unweighted row energy of `U`: `∑_t U_s t² ≤ 1/δ_s`. -/
lemma gsU_row_sq_sum_le (s : Fin k) :
    ∑ t : Fin k, (gsU A hA s t) ^ 2 ≤ (gsδ A hA s)⁻¹ := by
  have hδ := gsδ_pos A hA s.isLt
  have h := gsU_row_energy_mul_gsδ_le A hA s
  calc ∑ t : Fin k, (gsU A hA s t) ^ 2
      = (gsδ A hA s)⁻¹ * (gsδ A hA s * ∑ t : Fin k, (gsU A hA s t) ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
    _ ≤ (gsδ A hA s)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hδ.le)
    _ = (gsδ A hA s)⁻¹ := mul_one _

/-- Parseval on a pivot column: `‖v_t‖² = ∑_s δ_s U_s t²`. -/
lemma pivotVec_energy_eq (t : Fin k) :
    (pivotVec A hA t ⬝ᵥ pivotVec A hA t) =
      ∑ s : Fin k, gsδ A hA s * (gsU A hA s t) ^ 2 := by
  rw [pivotVec_dot_eq_sum]
  refine sum_congr rfl fun s _ => ?_
  ring

/-- Weighted column energy of `U` from column leverages `≤ 1`. -/
lemma gsU_col_weighted_sq_sum_le (t : Fin k) :
    ∑ s : Fin k, gsδ A hA s * (gsU A hA s t) ^ 2 ≤ 1 := by
  have h := col_energy_le A hA (cpqrChosen A hA t t.isLt)
  have hv : (fun i => A i (cpqrChosen A hA t t.isLt)) = pivotVec A hA t := rfl
  rw [hv, vecEnergy_eq_dot, pivotVec_energy_eq] at h
  exact h

/-- Unweighted column energy of `U`: `∑_s U_s t² ≤ n-k+1`.

This is the extra ℓ² budget from `R Rᵀ = I` plus the residual-energy lower
bound on every `δ_s`. It does not by itself close Path 1. -/
lemma gsU_col_sq_sum_le (t : Fin k) :
    ∑ s : Fin k, (gsU A hA s t) ^ 2 ≤ (n : ℝ) - k + 1 := by
  have hkn := orthogonalRows_le A hA
  have hC : (0 : ℝ) ≤ (n : ℝ) - k + 1 := by
    have : (k : ℝ) ≤ n := Nat.cast_le.mpr hkn
    linarith
  have hterm : ∀ s : Fin k,
      (gsU A hA s t) ^ 2 ≤
        ((n : ℝ) - k + 1) * (gsδ A hA s * (gsU A hA s t) ^ 2) := by
    intro s
    have hδ := gsδ_pos A hA s.isLt
    have hinv : (gsδ A hA s)⁻¹ ≤ (n : ℝ) - k + 1 :=
      (gsδ_inv_le A hA hkn s).trans (gsδ_ratio_le hkn s)
    have hnn : 0 ≤ gsδ A hA s * (gsU A hA s t) ^ 2 :=
      mul_nonneg hδ.le (sq_nonneg _)
    calc (gsU A hA s t) ^ 2
        = (gsδ A hA s)⁻¹ * (gsδ A hA s * (gsU A hA s t) ^ 2) := by
          rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
      _ ≤ ((n : ℝ) - k + 1) * (gsδ A hA s * (gsU A hA s t) ^ 2) :=
          mul_le_mul_of_nonneg_right hinv hnn
  calc ∑ s : Fin k, (gsU A hA s t) ^ 2
      ≤ ∑ s : Fin k,
          ((n : ℝ) - k + 1) * (gsδ A hA s * (gsU A hA s t) ^ 2) :=
        sum_le_sum fun s _ => hterm s
    _ = ((n : ℝ) - k + 1) *
          ∑ s : Fin k, gsδ A hA s * (gsU A hA s t) ^ 2 := by
        rw [← mul_sum]
    _ ≤ ((n : ℝ) - k + 1) * 1 :=
        mul_le_mul_of_nonneg_left (gsU_col_weighted_sq_sum_le A hA t) hC
    _ = (n : ℝ) - k + 1 := mul_one _

/-! ### Nearest-neighbor (bidiagonal) back-substitution -/

/-- Superdiagonal-only Gram–Schmidt coefficients: `U_s t = 0` unless
`t ∈ {s, s+1}`. This is a hypothesis on the factor `U`, not a static class
of matrices `A`. -/
def gsUBidiagonal : Prop :=
  ∀ s t : Fin k, (s : ℕ) + 1 < (t : ℕ) → gsU A hA s t = 0

lemma gsS_recurrence_bidiagonal (hbi : gsUBidiagonal A hA)
    {i j : Fin k} (hij : (i : ℕ) < (j : ℕ)) :
    gsS A hA i j =
      -(gsS A hA i ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ *
          gsU A hA ⟨(j : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ j) := by
  have hjk : (j : ℕ) - 1 < k := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
  rw [gsS_recurrence A hA hij]
  set jpred : Fin k := ⟨(j : ℕ) - 1, hjk⟩
  have hjpred_val : (jpred : ℕ) = (j : ℕ) - 1 := rfl
  have hjpred_mem : jpred ∈ Ico i j := by
    rw [mem_Ico, Fin.le_def, Fin.lt_def, hjpred_val]
    omega
  have herase :
      ∑ l ∈ (Ico i j).erase jpred, gsS A hA i l * gsU A hA l j = 0 := by
    refine sum_eq_zero fun l hl => ?_
    have ⟨hne, hlIco⟩ := mem_erase.mp hl
    have hlt : (l : ℕ) + 1 < (j : ℕ) := by
      have ⟨_, hlj⟩ := mem_Ico.mp hlIco
      have hval : (l : ℕ) ≠ (j : ℕ) - 1 := fun hco =>
        hne (Fin.ext (by simp [jpred, hco]))
      have : (l : ℕ) < (j : ℕ) := Fin.lt_def.mp hlj
      omega
    rw [hbi l j hlt, mul_zero]
  rw [← sum_erase_add (Ico i j) (fun l => gsS A hA i l * gsU A hA l j)
    hjpred_mem, herase, zero_add]

lemma gsS_abs_le_one_of_bidiagonal_aux (hbi : gsUBidiagonal A hA) (d : ℕ) :
    ∀ (i j : Fin k), (j : ℕ) - (i : ℕ) = d → |gsS A hA i j| ≤ 1 := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
    · have hjk : (j : ℕ) - 1 < k := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      have hrec := gsS_recurrence_bidiagonal A hA hbi hlt
      rw [hrec, abs_neg, abs_mul]
      have hval : ((⟨(j : ℕ) - 1, hjk⟩ : Fin k) : ℕ) = (j : ℕ) - 1 := rfl
      have hjpred : ((⟨(j : ℕ) - 1, hjk⟩ : Fin k) : ℕ) - (i : ℕ) < d := by
        rw [hval, ← hd]
        omega
      have hind := ih _ hjpred i ⟨(j : ℕ) - 1, hjk⟩ rfl
      have hU := gsU_entry_abs_le_one A hA ⟨(j : ℕ) - 1, hjk⟩ j
      exact (mul_le_mul hind hU (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
    · have hij : i = j := Fin.ext heq
      subst hij
      rw [gsS_diag, abs_one]
    · rw [gsS_lower A hA hgt, abs_zero]
      exact zero_le_one

/-- Nearest-neighbor chain: `|S i j| ≤ 1`. Each superdiagonal factor of `U`
has absolute value at most `1`, so a single coupling cannot produce
Businger–Golub doubling. -/
lemma gsS_abs_le_one_of_bidiagonal (hbi : gsUBidiagonal A hA)
    (i j : Fin k) : |gsS A hA i j| ≤ 1 :=
  gsS_abs_le_one_of_bidiagonal_aux A hA hbi ((j : ℕ) - (i : ℕ)) i j rfl

/-- Bidiagonal column energy of `S` is at most `ℓ+1`. -/
lemma gsS_col_sq_sum_le_of_bidiagonal (hbi : gsUBidiagonal A hA)
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
        (gsS_abs_le_one_of_bidiagonal A hA hbi s l)
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

/-- Inverse-Frobenius proxy under bidiagonal `U`.

This is a joint `poly(n,k)` bound on the **nearest-neighbor coefficient
pattern**, not a Path 1 theorem for every orthogonal-row matrix. Multi-neighbor
coupling remains open. Milestone E remains open. -/
theorem pivotGram_inv_trace_le_of_bidiagonal (hbi : gsUBidiagonal A hA) :
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
        have hE := gsS_col_sq_sum_le_of_bidiagonal A hA hbi l
        calc (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l) ^ 2
            ≤ ((n : ℝ) - k + 1) * ∑ s : Fin k, (gsS A hA s l) ^ 2 :=
              mul_le_mul_of_nonneg_right hδ hEnn
          _ ≤ ((n : ℝ) - k + 1) * (((l : ℕ) : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hE hC
    _ = ((n : ℝ) - k + 1) * ∑ l : Fin k, (((l : ℕ) : ℝ) + 1) := by
        rw [← mul_sum]
    _ = ((n : ℝ) - k + 1) * ((k : ℝ) * (k + 1) / 2) := by rw [hsum]
    _ = ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) := by ring

end RowOrthoQR

end StructuredColumnSelection
