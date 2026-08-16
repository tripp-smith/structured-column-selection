import StructuredColumnSelection.PrefixInverse

/-!
# Triangular inverse bound for orthogonal-row CPQR (Milestone E, Path 1 partial)

This module proves a Drmač–Gugercin / Gu–Eisenstat style *triangular* bound
for column-pivoted QR on an orthogonal-row matrix `A : ℝ^{k×n}` (`A * Aᵀ = 1`):

  `tr((Bᵀ B)⁻¹) ≤ n · (4^k + 6k - 1) / 9`,  where `B = selectedCols A (cpqrSet A)`.

The quantity `tr((BᵀB)⁻¹)` is the squared Frobenius norm `‖A_J⁻¹‖_F²` of the
selected square submatrix. The bound is **polynomial in `n` but exponential in
`k`** (it grows like `n · 4^k / 9`). It is therefore NOT a joint `poly(n, k)`
bound and does NOT close Milestone E; per the claim-discipline rule this file
exports honest `poly(n) · 2^k`-type statements only.

Proof outline (all machine-checked below):
1. The pivot-ordered Gram matrix `G' = Vᵀ V` (columns in CPQR pivot order)
   factors as `G' = Uᵀ Δ U` where `Δ = diag(δ)`, `δ t` is the `t`-th pivot
   residual, and `U` is unit upper triangular with `|U t l| ≤ 1`
   (Businger–Golub normalization; proved via an explicit Gram–Schmidt
   "Parseval" expansion of the selected-column projectors).
2. `δ t ≥ (k - t) / (n - t)` (residual energy average, `nextResidual_ge`).
3. The unit upper triangular inverse `S = U⁻¹` satisfies the entry bound
   `|S i j| ≤ 2^(j - i - 1)` (well-founded recursion on `j - i`).
4. `tr(G'⁻¹) = Σ_t δ_t⁻¹ ‖column t of S‖² ≤ n · Σ_t (1 + (4^t - 1)/3)`
   `= n (4^k + 6k - 1)/9`.
5. The pivot-ordered Gram is a simultaneous permutation of
   `selectedColGram A (cpqrSet A)`, and trace of the inverse is
   permutation-invariant.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-! ### Column-span API -/

/-- A `mulVec` is a combination of columns. -/
lemma mulVec_eq_sum_col {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ) (c : Fin t → ℝ) :
    B *ᵥ c = ∑ p : Fin t, c p • B.col p := by
  ext i
  simp only [mulVec_sum_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_comm]
  rfl

/-- Membership in the column span, concretely. -/
lemma mem_span_range_col_iff {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ)
    (y : Fin k → ℝ) :
    y ∈ Submodule.span ℝ (Set.range B.col) ↔ ∃ c : Fin t → ℝ, B *ᵥ c = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, rfl⟩ := hz
      exact ⟨Pi.single p 1, Matrix.mulVec_single_one B p⟩
    | zero => exact ⟨0, Matrix.mulVec_zero B⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨cx, hcx⟩ := ihx
      obtain ⟨cy, hcy⟩ := ihy
      exact ⟨cx + cy, by rw [Matrix.mulVec_add, hcx, hcy]⟩
    | smul a x _ ihx =>
      obtain ⟨cx, hcx⟩ := ihx
      exact ⟨a • cx, by rw [Matrix.mulVec_smul, hcx]⟩
  · rintro ⟨c, rfl⟩
    rw [mulVec_eq_sum_col]
    exact Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- Column spans are monotone in the index set. -/
lemma span_range_col_mono {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J J' : Finset (Fin n)} (hJJ : J ⊆ J') :
    Submodule.span ℝ (Set.range (selectedCols A J).col) ≤
      Submodule.span ℝ (Set.range (selectedCols A J').col) := by
  apply Submodule.span_mono
  rw [range_selectedCols_col, range_selectedCols_col]
  exact Set.image_mono (Finset.coe_subset.mpr hJJ)

/-- The selected column `j ∈ J` lies in the column span. -/
lemma col_mem_span_range {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} {j : Fin n} (hj : j ∈ J) :
    A.col j ∈ Submodule.span ℝ (Set.range (selectedCols A J).col) := by
  apply Submodule.subset_span
  rw [range_selectedCols_col]
  exact ⟨j, hj, rfl⟩

/-! ### Selected-projector algebra -/

/-- The selected-column Gram is symmetric. -/
lemma selectedColGram_transpose {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) :
    (selectedColGram A J)ᵀ = selectedColGram A J := by
  unfold selectedColGram
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The selected-column projector is symmetric. -/
lemma selectedProjector_transpose {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) :
    (selectedProjector A J)ᵀ = selectedProjector A J := by
  unfold selectedProjector
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, selectedColGram_transpose,
    Matrix.mul_assoc]

/-- Generic Gram projector `B (Bᵀ B)⁻¹ Bᵀ` is idempotent. -/
lemma gramProjector_idempotent {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ)
    (hG : (Bᵀ * B).det ≠ 0) :
    (B * (Bᵀ * B)⁻¹ * Bᵀ) * (B * (Bᵀ * B)⁻¹ * Bᵀ) = B * (Bᵀ * B)⁻¹ * Bᵀ := by
  have hGG : (Bᵀ * B)⁻¹ * (Bᵀ * B) = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hG)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Bᵀ B, ← Matrix.mul_assoc (Bᵀ * B)⁻¹ (Bᵀ * B), hGG,
    Matrix.one_mul]

/-- The selected-column projector is idempotent. -/
lemma selectedProjector_idempotent {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    selectedProjector A J * selectedProjector A J = selectedProjector A J := by
  unfold selectedProjector selectedColGram
  exact gramProjector_idempotent _ hG

/-- The projector applied to a vector is a column combination. -/
lemma selectedProjector_mem_span {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (x : Fin k → ℝ) :
    selectedProjector A J *ᵥ x ∈
      Submodule.span ℝ (Set.range (selectedCols A J).col) := by
  rw [mem_span_range_col_iff]
  refine ⟨(selectedColGram A J)⁻¹ *ᵥ ((selectedCols A J)ᵀ *ᵥ x), ?_⟩
  unfold selectedProjector
  rw [mulVec_mul_eq, mulVec_mul_eq]

/-- A generic Gram projector fixes columns of `B`. -/
lemma gramProjector_col {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ)
    (hG : (Bᵀ * B).det ≠ 0) (p : Fin t) :
    (B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ (B *ᵥ Pi.single p 1) = B *ᵥ Pi.single p 1 := by
  have hGG : (Bᵀ * B)⁻¹ * (Bᵀ * B) = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hG)
  rw [mulVec_mul_eq, mulVec_mul_eq,
    ← mulVec_mul_eq Bᵀ B (Pi.single p 1),
    ← mulVec_mul_eq (Bᵀ * B)⁻¹ (Bᵀ * B) (Pi.single p 1), hGG, one_mulVec_eq]

/-- The projector fixes selected columns. -/
lemma selectedProjector_col {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} {j : Fin n} (hj : j ∈ J)
    (hG : (selectedColGram A J).det ≠ 0) :
    selectedProjector A J *ᵥ A.col j = A.col j := by
  have hmem : j ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
    rw [Finset.range_orderEmbOfFin]; exact hj
  obtain ⟨p, hp⟩ := hmem
  have hcol : A.col j = selectedCols A J *ᵥ Pi.single p 1 := by
    rw [Matrix.mulVec_single_one, selectedCols_col, hp]
  rw [hcol]
  unfold selectedProjector selectedColGram
  exact gramProjector_col _ hG p

/-- Selected columns are orthogonal to `x - P x`. -/
lemma col_dot_sub_selectedProjector {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} {j : Fin n} (hj : j ∈ J)
    (hG : (selectedColGram A J).det ≠ 0) (x : Fin k → ℝ) :
    A.col j ⬝ᵥ (x - selectedProjector A J *ᵥ x) = 0 := by
  rw [dotProduct_sub_eq]
  have h2 : A.col j ⬝ᵥ (selectedProjector A J *ᵥ x) =
      ((selectedProjector A J)ᵀ *ᵥ A.col j) ⬝ᵥ x :=
    (transpose_mulVec_dot _ _ _).symm
  rw [selectedProjector_transpose, selectedProjector_col A hj hG] at h2
  rw [h2, sub_self]

/-- A vector in the column span that is orthogonal to every selected column
vanishes. -/
lemma eq_zero_of_mem_span_perp {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} {y : Fin k → ℝ}
    (hy : y ∈ Submodule.span ℝ (Set.range (selectedCols A J).col))
    (hperp : ∀ j ∈ J, A.col j ⬝ᵥ y = 0) : y = 0 := by
  rw [mem_span_range_col_iff] at hy
  obtain ⟨c, hc⟩ := hy
  have hBT : (selectedCols A J)ᵀ *ᵥ y = 0 := by
    ext p
    have hcol : (selectedCols A J).col p = A.col (J.orderEmbOfFin rfl p) :=
      selectedCols_col A J p
    have hy0 := hperp _ (Finset.orderEmbOfFin_mem J rfl p)
    have hentry : ((selectedCols A J)ᵀ *ᵥ y) p =
        (selectedCols A J).col p ⬝ᵥ y := by
      rw [mulVec_sum_eq, dotProduct_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    rw [hentry, hcol, hy0, Pi.zero_apply]
  have hyy : y ⬝ᵥ y = 0 := by
    have h := transpose_mulVec_dot (selectedCols A J) y c
    rw [hBT, zero_dotProduct] at h
    rw [hc] at h
    exact h.symm
  exact dotProduct_self_eq_zero.mp hyy

/-! ### Uniqueness of the projector action -/

/-- The vector `P x` is the unique vector in the column span whose difference
from `x` is orthogonal to every selected column. -/
lemma selectedProjector_mulVec_unique {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} (hG : (selectedColGram A J).det ≠ 0)
    (x y : Fin k → ℝ)
    (hy : y ∈ Submodule.span ℝ (Set.range (selectedCols A J).col))
    (hperp : ∀ j ∈ J, A.col j ⬝ᵥ (x - y) = 0) :
    selectedProjector A J *ᵥ x = y := by
  have hz_mem : selectedProjector A J *ᵥ x - y ∈
      Submodule.span ℝ (Set.range (selectedCols A J).col) :=
    Submodule.sub_mem _ (selectedProjector_mem_span A J x) hy
  have hz_perp : ∀ j ∈ J,
      A.col j ⬝ᵥ (selectedProjector A J *ᵥ x - y) = 0 := by
    intro j hj
    have h1 := col_dot_sub_selectedProjector A hj hG x
    have h2 := hperp j hj
    have hdeq : selectedProjector A J *ᵥ x - y =
        (x - y) - (x - selectedProjector A J *ᵥ x) := by
      ext i
      simp only [Pi.sub_apply]
      ring
    rw [hdeq, dotProduct_sub_eq, h2, h1, sub_zero]
  have hz := eq_zero_of_mem_span_perp A hz_mem hz_perp
  exact sub_eq_zero.mp hz

/-! ### Pivot bookkeeping for orthogonal-row CPQR -/

section OrthogonalRowGS

variable {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)

include hA in
/-- The Gram of any CPQR prefix iterate is nonsingular. -/
lemma gramIterate_det_ne_zero (t : ℕ) (ht : t ≤ k) :
    (selectedColGram A (cpqrIterate A t)).det ≠ 0 := by
  cases t with
  | zero =>
    have h1 : cpqrIterate A 0 = (∅ : Finset (Fin n)) := rfl
    rw [h1]
    have h : (selectedColGram A (∅ : Finset (Fin n))).det = 1 := Matrix.det_fin_zero
    rw [h]
    exact one_ne_zero
  | succ t => exact (cpqrIterate_invariant A hA (t + 1) ht).2 (Nat.succ_pos t)

include hA in
/-- Prefix iterates are nested. -/
lemma cpqrIterate_mono {s t : ℕ} (hst : s ≤ t) :
    t ≤ k → cpqrIterate A s ⊆ cpqrIterate A t := by
  induction t, hst using Nat.le_induction with
  | base => intro _; exact Subset.refl _
  | succ m hsm ih =>
    intro hmk
    refine Finset.Subset.trans (ih (Nat.le_of_succ_le hmk)) ?_
    obtain ⟨j, -, -, hins, -, -⟩ :=
      cpqrIterate_succ_spec A hA (Nat.lt_of_succ_le hmk)
    rw [hins]
    exact Finset.subset_insert j _

include hA in
/-- A projector over a larger iterate fixes the columns of a smaller one. -/
lemma projector_mul_selectedCols_mono {s t : ℕ} (hst : s ≤ t) (htk : t ≤ k) :
    selectedProjector A (cpqrIterate A t) * selectedCols A (cpqrIterate A s) =
      selectedCols A (cpqrIterate A s) := by
  have hGt := gramIterate_det_ne_zero A hA t htk
  ext i p
  have hfix : selectedProjector A (cpqrIterate A t) *ᵥ
        (selectedCols A (cpqrIterate A s)).col p =
      (selectedCols A (cpqrIterate A s)).col p := by
    rw [selectedCols_col]
    exact selectedProjector_col A
      (cpqrIterate_mono A hA hst htk (Finset.orderEmbOfFin_mem _ _ _)) hGt
  calc (selectedProjector A (cpqrIterate A t) *
          selectedCols A (cpqrIterate A s)) i p
      = ∑ l : Fin k, selectedProjector A (cpqrIterate A t) i l *
          (selectedCols A (cpqrIterate A s)).col p l := by
        simp only [Matrix.mul_apply, mulVec_sum_eq]
        rfl
    _ = (selectedProjector A (cpqrIterate A t) *ᵥ
          (selectedCols A (cpqrIterate A s)).col p) i := by
        rw [mulVec_sum_eq]
    _ = (selectedCols A (cpqrIterate A s)).col p i := by rw [hfix]
    _ = selectedCols A (cpqrIterate A s) i p := rfl

include hA in
/-- Projectors over nested iterates absorb: `P_s P_t = P_s` for `s ≤ t`. -/
lemma projector_mul_absorb {s t : ℕ} (hst : s ≤ t) (htk : t ≤ k) :
    selectedProjector A (cpqrIterate A s) * selectedProjector A (cpqrIterate A t) =
      selectedProjector A (cpqrIterate A s) := by
  set Q := selectedProjector A (cpqrIterate A t) with hQ
  have habs : Q * selectedCols A (cpqrIterate A s) = selectedCols A (cpqrIterate A s) :=
    projector_mul_selectedCols_mono A hA hst htk
  have hsymm : Qᵀ = Q := selectedProjector_transpose A _
  have hPdef : selectedProjector A (cpqrIterate A s) =
      selectedCols A (cpqrIterate A s) *
        ((selectedCols A (cpqrIterate A s))ᵀ * selectedCols A (cpqrIterate A s))⁻¹ *
          (selectedCols A (cpqrIterate A s))ᵀ := rfl
  rw [hPdef]
  have key : (selectedCols A (cpqrIterate A s))ᵀ * Q =
      (selectedCols A (cpqrIterate A s))ᵀ := by
    rw [← hsymm, ← Matrix.transpose_mul, habs]
  calc (selectedCols A (cpqrIterate A s) *
          ((selectedCols A (cpqrIterate A s))ᵀ * selectedCols A (cpqrIterate A s))⁻¹ *
            (selectedCols A (cpqrIterate A s))ᵀ) * Q
      = selectedCols A (cpqrIterate A s) *
          ((selectedCols A (cpqrIterate A s))ᵀ * selectedCols A (cpqrIterate A s))⁻¹ *
            ((selectedCols A (cpqrIterate A s))ᵀ * Q) := by
        simp only [Matrix.mul_assoc]
    _ = selectedCols A (cpqrIterate A s) *
          ((selectedCols A (cpqrIterate A s))ᵀ * selectedCols A (cpqrIterate A s))⁻¹ *
            (selectedCols A (cpqrIterate A s))ᵀ := by
        rw [key]

include hA in
/-- The `t`-th pivot column of `A`, as a vector. -/
noncomputable def pivotVec (t : Fin k) : Fin k → ℝ :=
  fun i => A i (cpqrChosen A hA t t.2)

lemma pivotVec_eq_col (t : Fin k) :
    pivotVec A hA t = A.col (cpqrChosen A hA t t.2) := rfl

/-- Unnormalized Gram–Schmidt direction `w_s` (junk `0` for `s ≥ k`). -/
noncomputable def gsW (s : ℕ) : Fin k → ℝ :=
  if h : s < k then
    (1 - selectedProjector A (cpqrIterate A s)) *ᵥ pivotVec A hA ⟨s, h⟩
  else 0

/-- Pivot residual `δ_s` (junk `1` for `s ≥ k`). -/
noncomputable def gsδ (s : ℕ) : ℝ :=
  if h : s < k then residualSq A (cpqrIterate A s) (cpqrChosen A hA s h) else 1

lemma gsW_eq {s : ℕ} (hs : s < k) :
    gsW A hA s =
      (1 - selectedProjector A (cpqrIterate A s)) *ᵥ pivotVec A hA ⟨s, hs⟩ :=
  dif_pos hs

lemma gsδ_eq {s : ℕ} (hs : s < k) :
    gsδ A hA s = residualSq A (cpqrIterate A s) (cpqrChosen A hA s hs) :=
  dif_pos hs

lemma gsδ_pos {s : ℕ} (hs : s < k) : 0 < gsδ A hA s := by
  rw [gsδ_eq A hA hs]
  exact (cpqrChosen_spec A hA hs).2.2.2

lemma gsδ_ne_zero {s : ℕ} (hs : s < k) : gsδ A hA s ≠ 0 :=
  (gsδ_pos A hA hs).ne'

lemma pivotVec_sub_projector {s : ℕ} (hs : s < k) :
    gsW A hA s =
      pivotVec A hA ⟨s, hs⟩ -
        selectedProjector A (cpqrIterate A s) *ᵥ pivotVec A hA ⟨s, hs⟩ := by
  rw [gsW_eq A hA hs, sub_mulVec_eq, one_mulVec_eq]

/-- The pivot column lies in the next iterate. -/
lemma pivot_mem_iterate_succ {t : ℕ} (ht : t < k) :
    cpqrChosen A hA t ht ∈ cpqrIterate A (t + 1) := by
  rw [(cpqrChosen_spec A hA ht).2.1]
  exact mem_insert_self _ _

include hA in
/-- `‖w_s‖² = δ_s`. -/
lemma gsW_sq {s : ℕ} (hs : s < k) :
    gsW A hA s ⬝ᵥ gsW A hA s = gsδ A hA s := by
  rw [gsW_eq A hA hs, gsδ_eq A hA hs]
  set P := selectedProjector A (cpqrIterate A s) with hP
  set v := pivotVec A hA ⟨s, hs⟩ with hv
  have hG := gramIterate_det_ne_zero A hA s (Nat.le_of_lt hs)
  have hidem : (1 - P) * (1 - P) = 1 - P := by
    have hPP : P * P = P := selectedProjector_idempotent A _ hG
    calc (1 - P) * (1 - P)
        = 1 * (1 - P) - P * (1 - P) := Matrix.sub_mul _ _ _
      _ = (1 - P) - (P * 1 - P * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - P) - (P - P) := by rw [Matrix.mul_one, hPP]
      _ = 1 - P := by rw [sub_self, sub_zero]
  have h1P : (1 - P)ᵀ = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, selectedProjector_transpose]
  have h1 := transpose_mulVec_dot ((1 - P)ᵀ) v ((1 - P) *ᵥ v)
  rw [Matrix.transpose_transpose] at h1
  -- h1 : ((1-P)*ᵥv) ⬝ᵥ ((1-P)*ᵥv) = v ⬝ᵥ ((1-P)ᵀ *ᵥ ((1-P)*ᵥv))
  rw [h1, h1P, ← mulVec_mul_eq, hidem]
  exact (residualSq_eq_quadForm A _ _ hG).symm

include hA in
/-- Gram–Schmidt directions are orthogonal. -/
lemma gsW_orth {s t : ℕ} (hst : s < t) (ht : t < k) :
    gsW A hA s ⬝ᵥ gsW A hA t = 0 := by
  have hsk : s < k := lt_trans hst ht
  rw [gsW_eq A hA hsk, gsW_eq A hA ht]
  set Ps := selectedProjector A (cpqrIterate A s) with hPs
  set Pt := selectedProjector A (cpqrIterate A t) with hPt
  set vs := pivotVec A hA ⟨s, hsk⟩ with hvs
  set vt := pivotVec A hA ⟨t, ht⟩ with hvt
  have hGt := gramIterate_det_ne_zero A hA t (Nat.le_of_lt ht)
  have habs : Ps * Pt = Ps :=
    projector_mul_absorb A hA (le_of_lt hst) (Nat.le_of_lt ht)
  have h1Ps : (1 - Ps)ᵀ = 1 - Ps := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, selectedProjector_transpose]
  have h1Pt : (1 - Pt)ᵀ = 1 - Pt := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, selectedProjector_transpose]
  have hcomp : (1 - Ps) * (1 - Pt) = 1 - Pt := by
    calc (1 - Ps) * (1 - Pt)
        = 1 * (1 - Pt) - Ps * (1 - Pt) := Matrix.sub_mul _ _ _
      _ = (1 - Pt) - (Ps * 1 - Ps * Pt) := by rw [Matrix.one_mul, Matrix.mul_sub]
      _ = (1 - Pt) - (Ps - Ps) := by rw [Matrix.mul_one, habs]
      _ = 1 - Pt := by rw [sub_self, sub_zero]
  have h1 : ((1 - Ps) *ᵥ vs) ⬝ᵥ ((1 - Pt) *ᵥ vt) =
      vs ⬝ᵥ (((1 - Ps) * (1 - Pt)) *ᵥ vt) := by
    have hmove := transpose_mulVec_dot ((1 - Ps)ᵀ) vs ((1 - Pt) *ᵥ vt)
    rw [Matrix.transpose_transpose] at hmove
    rw [hmove, h1Ps, mulVec_mul_eq]
  rw [h1, hcomp]
  -- now: vs ⬝ᵥ ((1 - Pt) *ᵥ vt) = 0 because Pt fixes vs
  have hmem : cpqrChosen A hA s hsk ∈ cpqrIterate A t :=
    cpqrIterate_mono A hA (Nat.succ_le_of_lt hst) (Nat.le_of_lt ht)
      (pivot_mem_iterate_succ A hA hsk)
  have hfix : Pt *ᵥ vs = vs := selectedProjector_col A hmem hGt
  have hz : (1 - Pt) *ᵥ vs = 0 := by
    rw [sub_mulVec_eq, one_mulVec_eq, hfix, sub_self]
  rw [← transpose_mulVec_dot (1 - Pt) vs vt, h1Pt, hz, zero_dotProduct]

include hA in
/-- The `s`-th Gram–Schmidt direction lies in the span of the first `s+1`
pivot columns. -/
lemma gsW_mem_span {s : ℕ} (hs : s < k) :
    gsW A hA s ∈
      Submodule.span ℝ (Set.range (selectedCols A (cpqrIterate A (s + 1))).col) := by
  rw [pivotVec_sub_projector A hA hs]
  have h1 : pivotVec A hA ⟨s, hs⟩ ∈
      Submodule.span ℝ (Set.range (selectedCols A (cpqrIterate A (s + 1))).col) :=
    col_mem_span_range A (pivot_mem_iterate_succ A hA hs)
  have h2 : selectedProjector A (cpqrIterate A s) *ᵥ pivotVec A hA ⟨s, hs⟩ ∈
      Submodule.span ℝ (Set.range (selectedCols A (cpqrIterate A (s + 1))).col) :=
    span_range_col_mono A
      (cpqrIterate_mono A hA (Nat.le_succ s) (Nat.succ_le_of_lt hs))
      (selectedProjector_mem_span A _ _)
  exact Submodule.sub_mem _ h1 h2

include hA in
/-- `v_s ⬝ᵥ w_s = δ_s` (the pivot column has unit component along its own
Gram–Schmidt direction). -/
lemma pivotVec_dot_gsW {s : ℕ} (hs : s < k) :
    pivotVec A hA ⟨s, hs⟩ ⬝ᵥ gsW A hA s = gsδ A hA s := by
  rw [gsW_eq A hA hs, gsδ_eq A hA hs]
  exact (residualSq_eq_quadForm A _ _
    (gramIterate_det_ne_zero A hA s (Nat.le_of_lt hs))).symm

include hA in
/-- Parseval expansion: the projector onto the first `t` pivot columns is the
sum of the normalized rank-one Gram–Schmidt projectors. -/
lemma projector_mulVec_eq_sum_gsW (t : ℕ) (htk : t ≤ k) (x : Fin k → ℝ) :
    selectedProjector A (cpqrIterate A t) *ᵥ x =
      ∑ s ∈ Finset.range t, ((x ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹) • gsW A hA s := by
  induction t with
  | zero =>
    have h0 : cpqrIterate A 0 = (∅ : Finset (Fin n)) := rfl
    rw [h0, selectedProjector_empty, Matrix.zero_mulVec, Finset.range_zero,
      Finset.sum_empty]
  | succ t ih =>
    have htk' : t ≤ k := Nat.le_of_succ_le htk
    have htk'' : t < k := Nat.lt_of_succ_le htk
    rw [Finset.sum_range_succ, ← ih htk']
    set P := selectedProjector A (cpqrIterate A t) with hP
    set w := gsW A hA t with hw
    set δt := gsδ A hA t with hδ
    set v := pivotVec A hA ⟨t, htk''⟩ with hv
    have hins : cpqrIterate A (t + 1) =
        insert (cpqrChosen A hA t htk'') (cpqrIterate A t) :=
      (cpqrChosen_spec A hA htk'').2.1
    have hG' := gramIterate_det_ne_zero A hA (t + 1) htk
    have hG := gramIterate_det_ne_zero A hA t htk'
    have hsub : cpqrIterate A t ⊆ cpqrIterate A (t + 1) :=
      cpqrIterate_mono A hA (Nat.le_succ t) htk
    have hw' : w = v - P *ᵥ v := by
      rw [hw, hv, pivotVec_sub_projector A hA htk'']
    have hwv : v ⬝ᵥ w = δt := by
      rw [hδ, hv]
      exact pivotVec_dot_gsW A hA htk''
    have hid : v ⬝ᵥ (x - P *ᵥ x) = x ⬝ᵥ w := by
      have hPsymm : Pᵀ = P := selectedProjector_transpose A _
      rw [dotProduct_sub_eq, hw', dotProduct_sub_eq]
      have hmove : v ⬝ᵥ (P *ᵥ x) = (P *ᵥ v) ⬝ᵥ x :=
        (transpose_mulVec_dot P v x).symm.trans (by rw [hPsymm])
      rw [hmove, dotProduct_comm x v, dotProduct_comm x (P *ᵥ v)]
    apply selectedProjector_mulVec_unique A hG' x (P *ᵥ x + ((x ⬝ᵥ w) * δt⁻¹) • w)
    · apply Submodule.add_mem
      · exact span_range_col_mono A hsub (selectedProjector_mem_span A _ x)
      · apply Submodule.smul_mem
        rw [hw']
        exact Submodule.sub_mem _
          (col_mem_span_range A (by rw [hins]; exact mem_insert_self _ _))
          (span_range_col_mono A hsub (selectedProjector_mem_span A _ _))
    · intro j hj
      rw [hins] at hj
      have hdecomp : x - (P *ᵥ x + ((x ⬝ᵥ w) * δt⁻¹) • w) =
          (x - P *ᵥ x) - ((x ⬝ᵥ w) * δt⁻¹) • w := by
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hdecomp, dotProduct_sub_eq, dotProduct_smul, smul_eq_mul]
      rcases mem_insert.mp hj with rfl | hjt
      · have hcolv : A.col (cpqrChosen A hA t htk'') = v := rfl
        rw [hcolv, hid, hwv, mul_assoc, inv_mul_cancel₀ (gsδ_ne_zero A hA htk'')]
        ring
      · have hperp0 := col_dot_sub_selectedProjector A hjt hG x
        have hfix : P *ᵥ A.col j = A.col j := selectedProjector_col A hjt hG
        have hzero : A.col j ⬝ᵥ w = 0 := by
          rw [hw, gsW_eq A hA htk'']
          rw [← transpose_mulVec_dot (1 - P) (A.col j) (pivotVec A hA ⟨t, htk''⟩)]
          have h1P : (1 - P)ᵀ = 1 - P := by
            rw [Matrix.transpose_sub, Matrix.transpose_one,
              selectedProjector_transpose]
          rw [h1P, sub_mulVec_eq, one_mulVec_eq, hfix, sub_self, zero_dotProduct]
        rw [hperp0, hzero, mul_zero, sub_zero]

/-! ### Chunk 3: the unit-triangular Gram factor `U` -/

include hA in
/-- The Gram–Schmidt coefficient matrix of the pivot columns, in pivot order:
`U s t = (v_t ⬝ᵥ w_s)/δ_s` for `s < t`, `1` on the diagonal, `0` below. -/
noncomputable def gsU : Matrix (Fin k) (Fin k) ℝ :=
  fun s t => if (s:ℕ) < (t:ℕ) then
    (pivotVec A hA t ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹
  else if s = t then 1 else 0

lemma gsU_apply (s t : Fin k) : gsU A hA s t =
    if (s:ℕ) < (t:ℕ) then (pivotVec A hA t ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹
    else if s = t then 1 else 0 := rfl

lemma gsU_apply_of_lt {s t : Fin k} (h : (s:ℕ) < (t:ℕ)) :
    gsU A hA s t = (pivotVec A hA t ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹ := by
  rw [gsU_apply, if_pos h]

lemma gsU_apply_diag (t : Fin k) : gsU A hA t t = 1 := by
  rw [gsU_apply, if_neg (lt_irrefl _), if_pos rfl]

lemma gsU_apply_of_gt {s t : Fin k} (h : (t:ℕ) < (s:ℕ)) : gsU A hA s t = 0 := by
  rw [gsU_apply, if_neg (not_lt_of_gt h), if_neg (show s ≠ t from ne_of_gt h)]

include hA in
/-- The pivot columns expand in the Gram–Schmidt directions with unit
diagonal coefficient. -/
lemma pivotVec_eq_sum_gsW (t : Fin k) :
    pivotVec A hA t =
      gsW A hA t + ∑ s ∈ Finset.range (t:ℕ),
        ((pivotVec A hA t ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹) • gsW A hA s := by
  have hPv := projector_mulVec_eq_sum_gsW A hA (t:ℕ) (Nat.le_of_lt t.isLt)
    (pivotVec A hA t)
  have hw := pivotVec_sub_projector A hA t.isLt
  rw [← hPv, hw]
  exact (sub_add_cancel _ _).symm

include hA in
/-- Summand for converting the `U`-expansion to a `Finset.range k` sum. -/
noncomputable def gsUSummand (t : Fin k) (m : ℕ) : Fin k → ℝ :=
  if m < (t:ℕ) then ((pivotVec A hA t ⬝ᵥ gsW A hA m) * (gsδ A hA m)⁻¹) • gsW A hA m
  else if m = (t:ℕ) then gsW A hA m else 0

lemma gsUSummand_apply (t : Fin k) (m : ℕ) : gsUSummand A hA t m =
    if m < (t:ℕ) then ((pivotVec A hA t ⬝ᵥ gsW A hA m) * (gsδ A hA m)⁻¹) • gsW A hA m
    else if m = (t:ℕ) then gsW A hA m else 0 := rfl

lemma gsW_orth' {s u : Fin k} (h : s ≠ u) : gsW A hA s ⬝ᵥ gsW A hA u = 0 := by
  have h' : (s:ℕ) ≠ (u:ℕ) := fun hc => h (Fin.ext hc)
  rcases lt_or_gt_of_ne h' with hlt | hgt
  · exact gsW_orth A hA hlt u.isLt
  · rw [dotProduct_comm]; exact gsW_orth A hA hgt s.isLt

include hA in
/-- The pivot columns expand over all Gram–Schmidt directions via `U`. -/
lemma pivotVec_eq_sum_gsU (t : Fin k) :
    pivotVec A hA t = ∑ s : Fin k, gsU A hA s t • gsW A hA s := by
  rw [pivotVec_eq_sum_gsW A hA t]
  have hconv1 : (∑ s : Fin k, gsU A hA s t • gsW A hA s) =
      ∑ m ∈ Finset.range k, (if h : m < k then gsUSummand A hA t m else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => if h : m < k then gsUSummand A hA t m
      else 0) k]
    apply Finset.sum_congr rfl; intro i _
    rw [dif_pos i.isLt, gsUSummand_apply, gsU_apply]
    by_cases h1 : (i:ℕ) < (t:ℕ)
    · simp only [if_pos h1]
    · by_cases h2 : i = t
      · have h2' : (i:ℕ) = (t:ℕ) := congrArg Fin.val h2
        simp only [if_neg h1, if_pos h2, if_pos h2', one_smul]
      · have h2' : (i:ℕ) ≠ (t:ℕ) := fun hc => h2 (Fin.ext hc)
        simp only [if_neg h1, if_neg h2, if_neg h2', zero_smul]
  have hconv2 : (∑ m ∈ Finset.range k, (if h : m < k then gsUSummand A hA t m
      else 0)) = ∑ m ∈ Finset.range k, gsUSummand A hA t m := by
    apply Finset.sum_congr rfl; intro m hm
    rw [dif_pos (Finset.mem_range.mp hm)]
  rw [hconv1, hconv2,
    ← Finset.sum_range_add_sum_Ico (gsUSummand A hA t) (Nat.le_of_lt t.isLt)]
  have hIco : (∑ m ∈ Finset.Ico (t:ℕ) k, gsUSummand A hA t m) = gsW A hA ↑t := by
    rw [Finset.sum_eq_single (t:ℕ)]
    · rw [gsUSummand_apply, if_neg (lt_irrefl _), if_pos rfl]
    · intro m hm hne
      have htm : (t:ℕ) < m :=
        lt_of_le_of_ne (Finset.mem_Ico.mp hm).1 fun hc => hne hc.symm
      rw [gsUSummand_apply, if_neg (not_lt_of_gt htm), if_neg (ne_of_gt htm)]
    · intro hcon
      exact absurd (Finset.mem_Ico.mpr ⟨le_refl _, t.isLt⟩) hcon
  rw [hIco, add_comm (gsW A hA ↑t) _, add_right_cancel_iff]
  apply Finset.sum_congr rfl; intro m hm
  rw [gsUSummand_apply, if_pos (Finset.mem_range.mp hm)]

include hA in
/-- Bilinear expansion of the pivot Gram entries along the orthogonal
Gram–Schmidt directions. -/
lemma pivotVec_dot_eq_sum (i j : Fin k) :
    pivotVec A hA i ⬝ᵥ pivotVec A hA j =
      ∑ s : Fin k, gsU A hA s i * (gsδ A hA s) * gsU A hA s j := by
  rw [pivotVec_eq_sum_gsU A hA i, pivotVec_eq_sum_gsU A hA j, sum_dotProduct]
  apply Finset.sum_congr rfl; intro s _
  rw [dotProduct_sum, Finset.sum_eq_single s]
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      gsW_sq A hA s.isLt]; ring
  · intro u _ hu
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      gsW_orth' A hA hu.symm]; ring
  · intro hcon; exact absurd (Finset.mem_univ s) hcon

include hA in
/-- Gram matrix of the pivot columns, in pivot order. -/
noncomputable def pivotGram : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => pivotVec A hA i ⬝ᵥ pivotVec A hA j

lemma pivotGram_apply (i j : Fin k) :
    pivotGram A hA i j = pivotVec A hA i ⬝ᵥ pivotVec A hA j := rfl

include hA in
/-- The `G' = Uᵀ Δ U` factorization of the pivot Gram matrix. -/
lemma pivotGram_eq :
    pivotGram A hA =
      (gsU A hA)ᵀ * Matrix.diagonal (fun s : Fin k => gsδ A hA s) * gsU A hA := by
  ext i j
  rw [pivotGram_apply, pivotVec_dot_eq_sum, Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro s _
  rw [Matrix.transpose_apply, Matrix.diagonal_mul]
  ring

include hA in
lemma gsU_isUpperTriangular : (gsU A hA).IsUpperTriangular := by
  intro i j hij
  exact gsU_apply_of_gt A hA hij

include hA in
lemma gsU_det : (gsU A hA).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (gsU_isUpperTriangular A hA),
    show (∏ i : Fin k, gsU A hA i i) = ∏ _i : Fin k, (1:ℝ) from
      Finset.prod_congr rfl fun i _ => gsU_apply_diag A hA i,
    Finset.prod_const_one]

include hA in
/-- `det G' = ∏ δ_s`. -/
lemma pivotGram_det : (pivotGram A hA).det = ∏ s : Fin k, gsδ A hA s := by
  rw [pivotGram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsU_det,
    Matrix.det_diagonal]
  simp

include hA in
lemma pivotGram_det_pos : 0 < (pivotGram A hA).det := by
  rw [pivotGram_det]
  exact Finset.prod_pos fun s _ => gsδ_pos A hA s.isLt

include hA in
lemma pivotGram_det_ne_zero : (pivotGram A hA).det ≠ 0 :=
  (pivotGram_det_pos A hA).ne'

/-! #### The `|U| ≤ 1` entry bound -/

include hA in
/-- Rank-one downdate of the residual along one Gram–Schmidt step. -/
lemma residualSq_downdate {s : ℕ} (hs : s < k) (j : Fin n) :
    residualSq A (cpqrIterate A (s + 1)) j =
      residualSq A (cpqrIterate A s) j - (A.col j ⬝ᵥ gsW A hA s)^2 * (gsδ A hA s)⁻¹ := by
  rw [show A.col j = (fun i => A i j) from rfl]
  have hG := gramIterate_det_ne_zero A hA s (Nat.le_of_lt hs)
  have hG' := gramIterate_det_ne_zero A hA (s + 1) hs
  rw [residualSq_eq_quadForm A _ j hG, residualSq_eq_quadForm A _ j hG']
  have hstep : (1 - selectedProjector A (cpqrIterate A (s + 1))) *ᵥ (fun i => A i j) =
      (1 - selectedProjector A (cpqrIterate A s)) *ᵥ (fun i => A i j) -
        (((fun i => A i j) ⬝ᵥ gsW A hA s) * (gsδ A hA s)⁻¹) • gsW A hA s := by
    rw [sub_mulVec_eq, sub_mulVec_eq, one_mulVec_eq,
      projector_mulVec_eq_sum_gsW A hA (s + 1) hs _,
      projector_mulVec_eq_sum_gsW A hA s (Nat.le_of_lt hs) _,
      Finset.sum_range_succ]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    ring
  rw [hstep, dotProduct_sub_eq, dotProduct_smul, smul_eq_mul]
  ring

include hA in
/-- Greedy maximality: later pivot columns have residual at most `δ_s` at
step `s`. -/
lemma residualSq_le_gsδ_of_lt {s t : Fin k} (h : s < t) :
    residualSq A (cpqrIterate A s) (cpqrChosen A hA t t.isLt) ≤ gsδ A hA s := by
  have hst : (s:ℕ) ≤ (t:ℕ) := le_of_lt h
  have hnot : cpqrChosen A hA t t.isLt ∉ cpqrIterate A s := fun hm =>
    (cpqrChosen_spec A hA t.isLt).1 (cpqrIterate_mono A hA hst (le_of_lt t.isLt) hm)
  have hne : (unused (cpqrIterate A ↑s)).Nonempty :=
    ⟨_, mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩⟩
  have hle := residualSq_le_maxResidual A hne (mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
  rw [← (cpqrChosen_spec A hA s.isLt).2.2.1] at hle
  rw [gsδ_eq A hA s.isLt]
  exact hle

include hA in
/-- Every entry of the Gram–Schmidt coefficient matrix has absolute value
at most `1` — the CPQR greedy maximality in coefficient form. -/
lemma gsU_entry_abs_le_one (s t : Fin k) : |gsU A hA s t| ≤ 1 := by
  by_cases hst : (s:ℕ) < (t:ℕ)
  · rw [gsU_apply_of_lt A hA hst, abs_mul,
      abs_of_pos (inv_pos.mpr (gsδ_pos A hA s.isLt))]
    have hδ := gsδ_pos A hA s.isLt
    rw [show (1:ℝ) = gsδ A hA s * (gsδ A hA s)⁻¹ from
      (mul_inv_cancel₀ (gsδ_ne_zero A hA s.isLt)).symm]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (inv_pos.mpr hδ))
    rw [← abs_of_pos hδ, ← sq_le_sq]
    have hdow := residualSq_downdate A hA s.isLt (cpqrChosen A hA t t.isLt)
    rw [← pivotVec_eq_col A hA t] at hdow
    have hgreedy := residualSq_le_gsδ_of_lt A hA hst
    have hnn := residualSq_nonneg A (cpqrIterate A (↑s + 1)) (cpqrChosen A hA t t.isLt)
    have h2 : (pivotVec A hA t ⬝ᵥ gsW A hA s)^2 * (gsδ A hA s)⁻¹ ≤ gsδ A hA s := by
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hδ)
    rw [mul_assoc, inv_mul_cancel₀ (gsδ_ne_zero A hA s.isLt), mul_one] at h3
    exact h3.trans_eq (pow_two _).symm
  · by_cases hseq : s = t
    · rw [hseq, gsU_apply_diag]; norm_num
    · have hgt : (t:ℕ) < (s:ℕ) := by
        rcases lt_or_gt_of_ne (fun hc => hseq (Fin.ext hc)) with h1 | h2
        · exact absurd h1 hst
        · exact h2
      rw [gsU_apply_of_gt A hA hgt]; norm_num

/-! ### Chunk 4: the inverse `S` of `U` (Neumann series) and its entry bound -/

include hA in
/-- The strict upper part of `U`: `N = 1 - U` is strictly upper triangular. -/
noncomputable def gsN : Matrix (Fin k) (Fin k) ℝ := 1 - gsU A hA

lemma gsN_apply (i j : Fin k) :
    gsN A hA i j = (1 : Matrix (Fin k) (Fin k) ℝ) i j - gsU A hA i j := rfl

lemma gsN_apply_diag (i : Fin k) : gsN A hA i i = 0 := by
  rw [gsN_apply, Matrix.one_apply_eq, gsU_apply_diag, sub_self]

lemma gsN_apply_of_gt {i j : Fin k} (h : (j:ℕ) < (i:ℕ)) : gsN A hA i j = 0 := by
  rw [gsN_apply, Matrix.one_apply_ne (show i ≠ j from fun hc => absurd (hc ▸ h)
    (lt_irrefl _)), gsU_apply_of_gt A hA h, sub_zero]

lemma gsN_apply_of_not_lt {i j : Fin k} (h : ¬ (i:ℕ) < (j:ℕ)) : gsN A hA i j = 0 := by
  rcases eq_or_lt_of_le (le_of_not_gt h) with heq | h'
  · rw [Fin.ext heq]; exact gsN_apply_diag A hA _
  · exact gsN_apply_of_gt A hA h'

include hA in
lemma gsN_abs_le_one (i j : Fin k) : |gsN A hA i j| ≤ 1 := by
  by_cases h : (i:ℕ) < (j:ℕ)
  · rw [gsN_apply, Matrix.one_apply_ne (show i ≠ j from ne_of_lt h), zero_sub,
      abs_neg]
    exact gsU_entry_abs_le_one A hA i j
  · rw [gsN_apply_of_not_lt A hA h]; norm_num

include hA in
/-- Strict triangularity propagates through powers: `(N^p) i j = 0` unless
`i + p ≤ j`. -/
lemma gsN_pow_apply_eq_zero (p : ℕ) {i j : Fin k} (h : (j:ℕ) < (i:ℕ) + p) :
    (gsN A hA ^ p) i j = 0 := by
  induction p generalizing i j with
  | zero =>
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun hc => by subst hc; simp at h)
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro l _
    by_cases h1 : (l:ℕ) < (i:ℕ) + p
    · rw [ih h1, zero_mul]
    · by_cases h2 : (l:ℕ) < (j:ℕ)
      · exfalso; omega
      · rw [gsN_apply_of_not_lt A hA h2, mul_zero]

include hA in
lemma gsN_pow_k : gsN A hA ^ k = 0 := by
  ext i j
  rw [gsN_pow_apply_eq_zero A hA k (by have hi := i.isLt; have hj := j.isLt; omega),
    Matrix.zero_apply]

/-- Finite geometric series with `1 - X`, valid in the (noncommutative) matrix
ring since only powers of `X` appear. -/
lemma geom_sum_one_sub {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ) (r : ℕ) :
    (∑ p ∈ Finset.range r, X ^ p) * (1 - X) = 1 - X ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, add_mul, ih, mul_sub, mul_one, ← pow_succ,
      sub_add_sub_cancel]

include hA in
/-- The Neumann-series inverse `S = Σ_{p < k} N^p` of `U = 1 - N`. -/
noncomputable def gsS : Matrix (Fin k) (Fin k) ℝ := ∑ p ∈ Finset.range k, gsN A hA ^ p

lemma gsS_apply (i j : Fin k) :
    gsS A hA i j = ∑ p ∈ Finset.range k, (gsN A hA ^ p) i j := by
  rw [show gsS A hA i j = (∑ p ∈ Finset.range k, gsN A hA ^ p) i j from rfl,
    Matrix.sum_apply]

include hA in
lemma gsS_mul_gsU : gsS A hA * gsU A hA = 1 := by
  have hU : gsU A hA = 1 - gsN A hA := (sub_sub_self 1 (gsU A hA)).symm
  calc gsS A hA * gsU A hA
      = (∑ p ∈ Finset.range k, gsN A hA ^ p) * gsU A hA := rfl
    _ = (∑ p ∈ Finset.range k, gsN A hA ^ p) * (1 - gsN A hA) := by rw [hU]
    _ = 1 - gsN A hA ^ k := geom_sum_one_sub _ _
    _ = 1 := by rw [gsN_pow_k, sub_zero]

include hA in
lemma gsU_inv : (gsU A hA)⁻¹ = gsS A hA := Matrix.inv_eq_left_inv (gsS_mul_gsU A hA)

include hA in
lemma gsS_diag (i : Fin k) : gsS A hA i i = 1 := by
  cases k with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ k' =>
    rw [gsS_apply, Finset.sum_range_succ', pow_zero, Matrix.one_apply_eq,
      show (∑ p ∈ Finset.range k', (gsN A hA ^ (p + 1)) i i) = 0 from
        Finset.sum_eq_zero fun p _ =>
          gsN_pow_apply_eq_zero A hA (p + 1) (by omega),
      zero_add]

include hA in
lemma gsS_lower {i j : Fin k} (h : (j:ℕ) < (i:ℕ)) : gsS A hA i j = 0 := by
  rw [gsS_apply]
  apply Finset.sum_eq_zero; intro p _
  cases p with
  | zero =>
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun hc => by subst hc; omega)
  | succ p' => exact gsN_pow_apply_eq_zero A hA (p' + 1) (by omega)

include hA in
/-- Back-substitution recurrence: `S i j = -∑_{l ∈ [i, j)} S i l · U l j`. -/
lemma gsS_recurrence {i j : Fin k} (hij : (i:ℕ) < (j:ℕ)) :
    gsS A hA i j = -∑ l ∈ Finset.Ico i j, gsS A hA i l * gsU A hA l j := by
  have h0 : (gsS A hA * gsU A hA) i j = 0 := by
    rw [gsS_mul_gsU A hA]
    exact Matrix.one_apply_ne (show i ≠ j from ne_of_lt hij)
  rw [Matrix.mul_apply] at h0
  have hrest : (∑ l : Fin k, gsS A hA i l * gsU A hA l j) =
      ∑ l ∈ Finset.Icc i j, gsS A hA i l * gsU A hA l j := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hl
    rcases hl with h1 | h1
    · rw [gsS_lower A hA h1, zero_mul]
    · rw [gsU_apply_of_gt A hA h1, mul_zero]
  rw [hrest, ← Finset.Ico_insert_right (show i ≤ j from le_of_lt hij),
    Finset.sum_insert (fun hm => absurd (Finset.mem_Ico.mp hm).2 (lt_irrefl _)),
    gsU_apply_diag, mul_one] at h0
  linarith

include hA in
/-- Businger–Golub entry bound, proved by strong induction on `j - i`. -/
lemma gsS_entry_abs_le_aux (d : ℕ) :
    ∀ (i j : Fin k), (j:ℕ) - (i:ℕ) = d → (i:ℕ) < (j:ℕ) →
      |gsS A hA i j| ≤ 2 ^ ((j:ℕ) - (i:ℕ) - 1) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro i j hd hij
    rw [gsS_recurrence A hA hij, abs_neg]
    have halign : (∑ l ∈ Finset.Ico i j, |gsS A hA i l|) =
        ∑ l ∈ Finset.Ico i j, (if hm : (l:ℕ) < k then |gsS A hA i ⟨l, hm⟩| else 0) :=
      Finset.sum_congr rfl fun l _ =>
        ((dif_pos l.isLt).trans
          (congrArg (fun x => |gsS A hA i x|) (Fin.ext rfl))).symm
    have hnotmem : (i:ℕ) ∉ Finset.Ico ((i:ℕ) + 1) (j:ℕ) := by
      intro hmem; exact absurd (Finset.mem_Ico.mp hmem).1 (by omega)
    calc |∑ l ∈ Finset.Ico i j, gsS A hA i l * gsU A hA l j|
        ≤ ∑ l ∈ Finset.Ico i j, |gsS A hA i l * gsU A hA l j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Finset.Ico i j, |gsS A hA i l| :=
          Finset.sum_le_sum fun l _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _)
              (gsU_entry_abs_le_one A hA l j)
      _ = ∑ m ∈ Finset.Ico (i:ℕ) (j:ℕ),
            (if hm : m < k then |gsS A hA i ⟨m, hm⟩| else 0) := by
          rw [halign, ← Fin.map_valEmbedding_Ico, Finset.sum_map]
          simp only [Fin.valEmbedding_apply]
      _ = 1 + ∑ m ∈ Finset.Ico ((i:ℕ) + 1) (j:ℕ),
            (if hm : m < k then |gsS A hA i ⟨m, hm⟩| else 0) := by
          rw [← Finset.insert_Ico_add_one_left_eq_Ico hij,
            Finset.sum_insert hnotmem, dif_pos i.isLt,
            show (⟨↑i, i.isLt⟩ : Fin k) = i from Fin.ext rfl, gsS_diag, abs_one]
      _ ≤ 1 + ∑ m ∈ Finset.Ico ((i:ℕ) + 1) (j:ℕ), (2:ℝ) ^ (m - (i:ℕ) - 1) := by
          apply add_le_add_right
          apply Finset.sum_le_sum; intro m hm
          have hmk : m < k := lt_trans (Finset.mem_Ico.mp hm).2 j.isLt
          have h1 : (i:ℕ) + 1 ≤ m := (Finset.mem_Ico.mp hm).1
          have h2 : m < (j:ℕ) := (Finset.mem_Ico.mp hm).2
          rw [dif_pos hmk]
          exact ih (m - (i:ℕ)) (by omega) i ⟨m, hmk⟩ rfl (by show (i:ℕ) < m; omega)
      _ = 1 + (2 ^ ((j:ℕ) - (i:ℕ) - 1) - 1) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have hgeo : ∑ q ∈ Finset.range ((j:ℕ) - ((i:ℕ) + 1)), (2:ℝ) ^ q =
              2 ^ ((j:ℕ) - (i:ℕ) - 1) - 1 := by
            rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1),
              show (j:ℕ) - ((i:ℕ) + 1) = (j:ℕ) - (i:ℕ) - 1 from by omega,
              show (2:ℝ) - 1 = 1 from by norm_num, div_one]
          rw [show ∑ q ∈ Finset.range ((j:ℕ) - ((i:ℕ) + 1)),
                (2:ℝ) ^ (((i:ℕ) + 1 + q) - (i:ℕ) - 1) =
              ∑ q ∈ Finset.range ((j:ℕ) - ((i:ℕ) + 1)), (2:ℝ) ^ q from
            Finset.sum_congr rfl fun q _ => by
              rw [show ((i:ℕ) + 1 + q) - (i:ℕ) - 1 = q from by omega]]
          rw [hgeo]
      _ = 2 ^ ((j:ℕ) - (i:ℕ) - 1) := by ring

include hA in
/-- The Businger–Golub bound `|S i j| ≤ 2^{j-i-1}` for `i < j`. -/
lemma gsS_entry_abs_le {i j : Fin k} (h : (i:ℕ) < (j:ℕ)) :
    |gsS A hA i j| ≤ 2 ^ ((j:ℕ) - (i:ℕ) - 1) :=
  gsS_entry_abs_le_aux A hA ((j:ℕ) - (i:ℕ)) i j rfl h

/-! ### Chunk 5: trace assembly -/

include hA in
/-- Entry bound for all `i j`: zero below the diagonal, `2^(j-i-1)` on/above it. -/
lemma gsS_entry_abs_le_all (i j : Fin k) :
    |gsS A hA i j| ≤ if (j:ℕ) < (i:ℕ) then 0 else 2 ^ ((j:ℕ) - (i:ℕ) - 1) := by
  by_cases h : (j:ℕ) < (i:ℕ)
  · rw [if_pos h, gsS_lower A hA h, abs_zero]
  · rw [if_neg h]
    rcases eq_or_lt_of_le (Nat.not_lt.mp h) with heq | hlt
    · have hiji : i = j := Fin.ext heq
      subst hiji
      exact le_of_eq (by
        rw [gsS_diag A hA i, abs_one,
          show (i:ℕ) - (i:ℕ) - 1 = 0 from by omega, pow_zero])
    · exact gsS_entry_abs_le A hA hlt

include hA in
/-- Column `l` of `S` has squared norm at most `(4^l + 2)/3`: the diagonal
contributes `1` and the strict upper part a geometric sum `(4^l - 1)/3`. -/
lemma gsS_col_sq_sum_le (l : Fin k) :
    ∑ s : Fin k, (gsS A hA s l)^2 ≤ (4 ^ (l:ℕ) + 2) / 3 := by
  have hterm : ∀ s : Fin k, (gsS A hA s l)^2 ≤
      if (s:ℕ) ≤ (l:ℕ) then (4:ℝ)^((l:ℕ)-(s:ℕ)-1) else 0 := by
    intro s
    rw [← sq_abs]
    refine (pow_le_pow_left₀ (abs_nonneg _) (gsS_entry_abs_le_all A hA s l) 2).trans ?_
    by_cases h : (l:ℕ) < (s:ℕ)
    · rw [if_pos h, if_neg (by omega : ¬ (s:ℕ) ≤ (l:ℕ))]
      norm_num
    · rw [if_neg h, if_pos (Nat.not_lt.mp h)]
      exact le_of_eq (by
        rw [show (4:ℝ) = 2^2 from by norm_num, ← pow_mul, ← pow_mul,
          mul_comm ((l:ℕ)-(s:ℕ)-1) 2])
  calc ∑ s : Fin k, (gsS A hA s l)^2
      ≤ ∑ s : Fin k, if (s:ℕ) ≤ (l:ℕ) then (4:ℝ)^((l:ℕ)-(s:ℕ)-1) else 0 :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = ∑ s ∈ Finset.range ((l:ℕ)+1), (4:ℝ)^((l:ℕ)-s-1) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun x : ℕ => if x ≤ (l:ℕ) then (4:ℝ)^((l:ℕ)-x-1) else 0) k]
        have hsub : Finset.range ((l:ℕ)+1) ⊆ Finset.range k := by
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        refine (Finset.sum_subset hsub ?_).symm.trans ?_
        · intro s hsk hs
          rw [Finset.mem_range] at hsk hs
          show (if (s:ℕ) ≤ (l:ℕ) then (4:ℝ)^((l:ℕ)-s-1) else 0) = 0
          exact if_neg (by omega)
        · refine Finset.sum_congr rfl fun s hs => ?_
          rw [Finset.mem_range] at hs
          show (if (s:ℕ) ≤ (l:ℕ) then (4:ℝ)^((l:ℕ)-s-1) else 0) = _
          exact if_pos (by omega)
    _ = 1 + ∑ q ∈ Finset.range (l:ℕ), (4:ℝ)^q := by
        rw [Finset.sum_range_succ,
          show (4:ℝ)^((l:ℕ)-(l:ℕ)-1) = 1 from by
            rw [show (l:ℕ)-(l:ℕ)-1 = 0 from by omega, pow_zero],
          add_comm]
        congr 1
        have hrefl : ∑ s ∈ Finset.range (l:ℕ), (4:ℝ)^((l:ℕ)-s-1) =
            ∑ s ∈ Finset.range (l:ℕ), (4:ℝ)^((l:ℕ)-1-s) :=
          Finset.sum_congr rfl fun s hs => by
            rw [Finset.mem_range] at hs
            congr 1
            omega
        rw [hrefl]
        exact Finset.sum_range_reflect _ _
    _ = (4 ^ (l:ℕ) + 2) / 3 := by
        rw [geom_sum_eq (by norm_num : (4:ℝ) ≠ 1),
          show (4:ℝ) - 1 = 3 from by norm_num]
        ring

include hA in
/-- The inverse of the pivot Gram matrix: `G'⁻¹ = S Δ⁻¹ Sᵀ`. -/
lemma pivotGram_inv_eq :
    (pivotGram A hA)⁻¹ =
      gsS A hA * Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ := by
  apply Matrix.inv_eq_right_inv
  have hUS : gsU A hA * gsS A hA = 1 := mul_eq_one_comm.mp (gsS_mul_gsU A hA)
  have hΔ : Matrix.diagonal (fun s : Fin k => gsδ A hA s) *
      Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal,
      show (fun s : Fin k => gsδ A hA s * (gsδ A hA s)⁻¹) = fun _ => (1:ℝ) from
        funext fun s => mul_inv_cancel₀ (gsδ_ne_zero A hA s.isLt),
      Matrix.diagonal_one]
  calc pivotGram A hA *
        (gsS A hA * Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ)
      = (gsU A hA)ᵀ * Matrix.diagonal (fun s : Fin k => gsδ A hA s) *
          (gsU A hA * (gsS A hA * Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) *
            (gsS A hA)ᵀ)) := by
        rw [pivotGram_eq, Matrix.mul_assoc]
    _ = (gsU A hA)ᵀ * (Matrix.diagonal (fun s : Fin k => gsδ A hA s) *
          (Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ)) := by
        rw [show gsU A hA * (gsS A hA *
              Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ) =
            Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ from by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUS, Matrix.one_mul]]
        rw [Matrix.mul_assoc]
    _ = 1 := by
        rw [← Matrix.mul_assoc (Matrix.diagonal fun s : Fin k => gsδ A hA s)
            (Matrix.diagonal fun s : Fin k => (gsδ A hA s)⁻¹) ((gsS A hA)ᵀ),
          hΔ, Matrix.one_mul, ← Matrix.transpose_mul, gsS_mul_gsU, Matrix.transpose_one]

include hA in
/-- Trace of the inverse pivot Gram in terms of `S`-column energies:
`tr(G'⁻¹) = ∑_l δ_l⁻¹ · ‖S-column l‖²`. -/
lemma pivotGram_inv_trace :
    ((pivotGram A hA)⁻¹).trace =
      ∑ l : Fin k, (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l)^2 := by
  rw [pivotGram_inv_eq]
  have h1 : ∀ i : Fin k,
      (gsS A hA * Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ) i i =
        ∑ l : Fin k, gsS A hA i l * (gsδ A hA l)⁻¹ * gsS A hA i l := by
    intro i
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  calc (gsS A hA * Matrix.diagonal (fun s : Fin k => (gsδ A hA s)⁻¹) * (gsS A hA)ᵀ).trace
      = ∑ i : Fin k, ∑ l : Fin k, gsS A hA i l * (gsδ A hA l)⁻¹ * gsS A hA i l := by
        simp only [Matrix.trace]
        exact Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ l : Fin k, (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l)^2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

include hA in
/-- Inverse pivot residual bound from residual energy: `1/δ_l ≤ (n-l)/(k-l)`. -/
lemma gsδ_inv_le (hkn : k ≤ n) (l : Fin k) :
    (gsδ A hA l)⁻¹ ≤ ((n:ℝ) - (l:ℕ)) / ((k:ℝ) - (l:ℕ)) := by
  have hδ : (0:ℝ) < gsδ A hA l := gsδ_pos A hA l.isLt
  have hge : ((k:ℝ) - (l:ℕ)) / ((n:ℝ) - (l:ℕ)) ≤ gsδ A hA l := by
    rw [gsδ_eq A hA l.isLt]
    exact cpqr_pivot_residual_ge A hA l.isLt
  have hposr : (0:ℝ) < ((k:ℝ) - (l:ℕ)) / ((n:ℝ) - (l:ℕ)) := by
    apply div_pos
    · exact sub_pos.mpr (Nat.cast_lt.mpr l.isLt)
    · exact sub_pos.mpr (Nat.cast_lt.mpr (lt_of_lt_of_le l.isLt hkn))
  calc (gsδ A hA l)⁻¹ ≤ (((k:ℝ) - (l:ℕ)) / ((n:ℝ) - (l:ℕ)))⁻¹ :=
        (inv_le_inv₀ hδ hposr).mpr hge
    _ = ((n:ℝ) - (l:ℕ)) / ((k:ℝ) - (l:ℕ)) := inv_div _ _

/-- The ratio `(n-l)/(k-l)` is increasing in `l` on `l ≤ k-1`, so it is at
most its value at `l = k-1`, namely `n-k+1`. -/
lemma gsδ_ratio_le {k n : ℕ} (hkn : k ≤ n) (l : Fin k) :
    ((n:ℝ) - (l:ℕ)) / ((k:ℝ) - (l:ℕ)) ≤ (n:ℝ) - k + 1 := by
  have hnum : (0:ℝ) < (k:ℝ) - (l:ℕ) := sub_pos.mpr (Nat.cast_lt.mpr l.isLt)
  rw [div_le_iff₀ hnum]
  have h1 : (k:ℝ) ≤ n := Nat.cast_le.mpr hkn
  have h2 : (l:ℝ) + 1 ≤ k := by exact_mod_cast l.isLt
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

include hA in
/-- **Trace bound (Drmač–Gugercin / Gu–Eisenstat style).** For an orthogonal-row
matrix, the pivot-ordered CPQR Gram matrix satisfies

`tr((G')⁻¹) ≤ (n - k + 1) · (4^k + 6k - 1) / 9`.

This is polynomial in `n` but exponential in `k` (it grows like `n · 4^k / 9`),
so it is NOT a joint `poly(n, k)` bound and does NOT close Milestone E. -/
theorem pivotGram_inv_trace_le :
    ((pivotGram A hA)⁻¹).trace ≤
      ((n:ℝ) - k + 1) * ((4:ℝ)^k + 6*k - 1) / 9 := by
  have hkn := orthogonalRows_le A hA
  rw [pivotGram_inv_trace]
  calc ∑ l : Fin k, (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l)^2
      ≤ ∑ l : Fin k, ((n:ℝ) - k + 1) * ((4^(l:ℕ) + 2)/3) := by
        refine Finset.sum_le_sum fun l _ => ?_
        have hcolnn : (0:ℝ) ≤ (4^(l:ℕ) + 2)/3 := by positivity
        calc (gsδ A hA l)⁻¹ * ∑ s : Fin k, (gsS A hA s l)^2
            ≤ (gsδ A hA l)⁻¹ * ((4^(l:ℕ)+2)/3) :=
              mul_le_mul_of_nonneg_left (gsS_col_sq_sum_le A hA l)
                (inv_nonneg.mpr (gsδ_pos A hA l.isLt).le)
          _ ≤ (((n:ℝ)-(l:ℕ))/((k:ℝ)-(l:ℕ))) * ((4^(l:ℕ)+2)/3) :=
              mul_le_mul_of_nonneg_right (gsδ_inv_le A hA hkn l) hcolnn
          _ ≤ ((n:ℝ)-k+1) * ((4^(l:ℕ)+2)/3) :=
              mul_le_mul_of_nonneg_right (gsδ_ratio_le hkn l) hcolnn
    _ = ((n:ℝ) - k + 1) * ((4:ℝ)^k + 6*k - 1) / 9 := by
        rw [mul_div_assoc, ← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_div, Finset.sum_add_distrib]
        have hgeo : ∑ l : Fin k, (4:ℝ)^(l:ℕ) = ((4:ℝ)^k - 1)/3 := by
          rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => (4:ℝ)^x) k,
            geom_sum_eq (by norm_num : (4:ℝ) ≠ 1),
            show (4:ℝ) - 1 = 3 from by norm_num]
        rw [hgeo]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring

end OrthogonalRowGS

end StructuredColumnSelection
