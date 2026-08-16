import StructuredColumnSelection.TriangularBound

/-!
# Residual monotonicity and rank-1 downdate

If `J ⊆ J'` and both selected Grams are invertible, the squared residual of
any column is antitone in the index set: projecting off a larger independent
span cannot increase `residualSq`. Nested selected projectors absorb, so the
complements compose and the residual energy of `J'` is the energy of an
orthogonal projection of the residual of `J`.

Inserting one independent column is a rank-1 Gram–Schmidt step: the residual
after the insert equals the previous residual minus the squared coefficient
along the projector increment. Specializing to a CPQR pivot recovers the
inline identity used in `TriangularBound.lean`.

These are algebraic projector identities. They are **not** a joint
`poly(n, k)` inverse-norm bound, they do **not** close Milestone E, and they
do **not** solve Simons Problem 4.1.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-! ### Nested projector absorption -/

/-- A projector over a larger independent set fixes the columns of a subset. -/
lemma selectedProjector_mul_selectedCols {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J J' : Finset (Fin n)} (hJJ : J ⊆ J')
    (hG' : (selectedColGram A J').det ≠ 0) :
    selectedProjector A J' * selectedCols A J = selectedCols A J := by
  ext i p
  have hfix : selectedProjector A J' *ᵥ (selectedCols A J).col p =
      (selectedCols A J).col p := by
    rw [selectedCols_col]
    exact selectedProjector_col A (hJJ (Finset.orderEmbOfFin_mem _ _ _)) hG'
  calc (selectedProjector A J' * selectedCols A J) i p
      = ∑ l : Fin k, selectedProjector A J' i l *
          (selectedCols A J).col p l := by
        simp only [Matrix.mul_apply]
        rfl
    _ = (selectedProjector A J' *ᵥ (selectedCols A J).col p) i := by
        rw [mulVec_sum_eq]
    _ = (selectedCols A J).col p i := by rw [hfix]
    _ = selectedCols A J i p := rfl

/-- Nested independent projectors absorb: `P_J P_{J'} = P_J` when `J ⊆ J'`. -/
lemma selectedProjector_absorb {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J J' : Finset (Fin n)} (hJJ : J ⊆ J')
    (_hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A J').det ≠ 0) :
    selectedProjector A J * selectedProjector A J' = selectedProjector A J := by
  set Q := selectedProjector A J'
  have habs : Q * selectedCols A J = selectedCols A J :=
    selectedProjector_mul_selectedCols A hJJ hG'
  have hsymm : Qᵀ = Q := selectedProjector_transpose A _
  have hPdef : selectedProjector A J =
      selectedCols A J *
        ((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *
          (selectedCols A J)ᵀ := rfl
  rw [hPdef]
  have key : (selectedCols A J)ᵀ * Q = (selectedCols A J)ᵀ := by
    rw [← hsymm, ← Matrix.transpose_mul, habs]
  calc (selectedCols A J *
          ((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *
            (selectedCols A J)ᵀ) * Q
      = selectedCols A J *
          ((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *
            ((selectedCols A J)ᵀ * Q) := by
        simp only [Matrix.mul_assoc]
    _ = selectedCols A J *
          ((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *
            (selectedCols A J)ᵀ := by
        rw [key]

/-- The complementary projectors compose: `(I-P_{J'})(I-P_J) = I-P_{J'}`. -/
lemma one_sub_selectedProjector_comp {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J J' : Finset (Fin n)} (hJJ : J ⊆ J')
    (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A J').det ≠ 0) :
    (1 - selectedProjector A J') * (1 - selectedProjector A J) =
      1 - selectedProjector A J' := by
  set P := selectedProjector A J
  set Q := selectedProjector A J'
  have hPQ : P * Q = P := selectedProjector_absorb A hJJ hG hG'
  have hPt : Pᵀ = P := selectedProjector_transpose A J
  have hQt : Qᵀ = Q := selectedProjector_transpose A J'
  have hQP : Q * P = P := by
    calc Q * P
        = Qᵀ * Pᵀ := by rw [hQt, hPt]
      _ = (P * Q)ᵀ := (Matrix.transpose_mul _ _).symm
      _ = Pᵀ := by rw [hPQ]
      _ = P := hPt
  calc (1 - Q) * (1 - P)
      = 1 * (1 - P) - Q * (1 - P) := Matrix.sub_mul _ _ _
    _ = (1 - P) - (Q * 1 - Q * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
    _ = (1 - P) - (Q - P) := by rw [Matrix.mul_one, hQP]
    _ = 1 - Q := sub_sub_sub_cancel_right _ _ _

lemma one_sub_selectedProjector_idempotent {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    (1 - selectedProjector A J) * (1 - selectedProjector A J) =
      1 - selectedProjector A J := by
  set P := selectedProjector A J
  have hPP : P * P = P := selectedProjector_idempotent A J hG
  calc (1 - P) * (1 - P)
      = 1 * (1 - P) - P * (1 - P) := Matrix.sub_mul _ _ _
    _ = (1 - P) - (P * 1 - P * P) := by rw [Matrix.one_mul, Matrix.mul_sub]
    _ = (1 - P) - (P - P) := by rw [Matrix.mul_one, hPP]
    _ = 1 - P := by rw [sub_self, sub_zero]

lemma one_sub_selectedProjector_transpose {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) :
    (1 - selectedProjector A J)ᵀ = 1 - selectedProjector A J := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, selectedProjector_transpose]

lemma selectedProjector_quadForm {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (x : Fin k → ℝ) :
    (x ⬝ᵥ (selectedProjector A J *ᵥ x)) =
      ((selectedProjector A J *ᵥ x) ⬝ᵥ (selectedProjector A J *ᵥ x)) := by
  have hPP := selectedProjector_idempotent A J hG
  have hPt := selectedProjector_transpose A J
  have h :=
    transpose_mulVec_dot (selectedProjector A J)
      (selectedProjector A J *ᵥ x) x
  rw [hPt, ← mulVec_mul_eq, hPP] at h
  rw [dotProduct_comm]
  exact h

lemma one_sub_selectedProjector_quadForm {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) (x : Fin k → ℝ) :
    (x ⬝ᵥ ((1 - selectedProjector A J) *ᵥ x)) =
      (((1 - selectedProjector A J) *ᵥ x) ⬝ᵥ
        ((1 - selectedProjector A J) *ᵥ x)) := by
  have hidem := one_sub_selectedProjector_idempotent A J hG
  have h1P := one_sub_selectedProjector_transpose A J
  have h :=
    transpose_mulVec_dot (1 - selectedProjector A J)
      ((1 - selectedProjector A J) *ᵥ x) x
  rw [h1P, ← mulVec_mul_eq, hidem] at h
  rw [dotProduct_comm]
  exact h

lemma residualSq_eq_energy {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (j : Fin n)
    (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j =
      (((1 - selectedProjector A J) *ᵥ fun i => A i j) ⬝ᵥ
        ((1 - selectedProjector A J) *ᵥ fun i => A i j)) := by
  rw [residualSq_eq_quadForm A J j hG]
  exact one_sub_selectedProjector_quadForm A J hG _

lemma dotProduct_self_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct_eq]
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Orthogonal projection cannot increase Euclidean energy. -/
lemma one_sub_selectedProjector_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) (y : Fin k → ℝ) :
    (((1 - selectedProjector A J) *ᵥ y) ⬝ᵥ
      ((1 - selectedProjector A J) *ᵥ y)) ≤ (y ⬝ᵥ y) := by
  have hQ :
      (((1 - selectedProjector A J) *ᵥ y) ⬝ᵥ
        ((1 - selectedProjector A J) *ᵥ y)) =
        (y ⬝ᵥ ((1 - selectedProjector A J) *ᵥ y)) :=
    (one_sub_selectedProjector_quadForm A J hG y).symm
  have hsplit :
      (y ⬝ᵥ ((1 - selectedProjector A J) *ᵥ y)) =
        (y ⬝ᵥ y) - (y ⬝ᵥ (selectedProjector A J *ᵥ y)) := by
    rw [sub_mulVec_eq, one_mulVec_eq, dotProduct_sub_eq]
  have hPnn : 0 ≤ y ⬝ᵥ (selectedProjector A J *ᵥ y) := by
    rw [selectedProjector_quadForm A J hG y]
    exact dotProduct_self_nonneg _
  rw [hQ, hsplit]
  linarith

/-- Residual is antitone in the independent index set. This is not an
inverse-norm bound. -/
theorem residualSq_antitone {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J J' : Finset (Fin n)} (hJJ : J ⊆ J')
    (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A J').det ≠ 0) (j : Fin n) :
    residualSq A J' j ≤ residualSq A J j := by
  rw [residualSq_eq_energy A J j hG, residualSq_eq_energy A J' j hG']
  set x := fun i => A i j
  have hcomp :
      (1 - selectedProjector A J') *ᵥ x =
        (1 - selectedProjector A J') *ᵥ ((1 - selectedProjector A J) *ᵥ x) := by
    rw [← mulVec_mul_eq, one_sub_selectedProjector_comp A hJJ hG hG']
  rw [hcomp]
  exact one_sub_selectedProjector_energy_le A J' hG' _

/-! ### Rank-1 residual downdate -/

/-- Unnormalized residual direction of column `p` after projecting off
`span(A_J)`. -/
noncomputable def residualVec {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (p : Fin n) : Fin k → ℝ :=
  (1 - selectedProjector A J) *ᵥ A.col p

lemma residualVec_eq {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (p : Fin n) :
    residualVec A J p = (1 - selectedProjector A J) *ᵥ A.col p :=
  rfl

lemma residualVec_sub {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (p : Fin n) :
    residualVec A J p =
      A.col p - selectedProjector A J *ᵥ A.col p := by
  rw [residualVec_eq, sub_mulVec_eq, one_mulVec_eq]

lemma residualVec_sq {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (p : Fin n)
    (hG : (selectedColGram A J).det ≠ 0) :
    (residualVec A J p ⬝ᵥ residualVec A J p) = residualSq A J p := by
  unfold residualVec
  have hidem := one_sub_selectedProjector_idempotent A J hG
  have h1P := one_sub_selectedProjector_transpose A J
  have h1 :=
    transpose_mulVec_dot ((1 - selectedProjector A J)ᵀ) (A.col p)
      ((1 - selectedProjector A J) *ᵥ A.col p)
  rw [Matrix.transpose_transpose] at h1
  rw [h1, h1P, ← mulVec_mul_eq, hidem]
  exact (residualSq_eq_quadForm A J p hG).symm

/-- An invertible inserted Gram forces a strictly positive residual, so the
new column is outside the previous span. -/
lemma residualSq_ne_zero_of_insert_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {p : Fin n}
    (hp : p ∉ J) (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A (insert p J)).det ≠ 0) :
    residualSq A J p ≠ 0 := by
  intro hz
  have hmem := col_mem_span_of_residualSq_eq_zero A (Or.inr hG) hz
  have hspan :
      Submodule.span ℝ (Set.range (selectedCols A (insert p J)).col) =
        Submodule.span ℝ (Set.range (selectedCols A J).col) := by
    rw [range_selectedCols_insert]
    exact Submodule.span_insert_eq_span hmem
  have hBrank : (selectedCols A J).rank = J.card := by
    have : (selectedColGram A J).rank = Fintype.card (Fin J.card) :=
      Matrix.rank_of_det_ne_zero hG
    simpa [selectedColGram, Matrix.rank_transpose_mul_self, Fintype.card_fin]
      using this
  have hB'rank : (selectedCols A (insert p J)).rank = (insert p J).card := by
    have : (selectedColGram A (insert p J)).rank =
        Fintype.card (Fin (insert p J).card) :=
      Matrix.rank_of_det_ne_zero hG'
    simpa [selectedColGram, Matrix.rank_transpose_mul_self, Fintype.card_fin]
      using this
  have hcard : (insert p J).card = J.card + 1 := card_insert_of_notMem hp
  have hrank :
      (selectedCols A (insert p J)).rank = (selectedCols A J).rank := by
    rw [Matrix.rank_eq_finrank_span_cols, hspan,
      ← Matrix.rank_eq_finrank_span_cols]
  omega

/-- Rank-1 update of the selected projector after inserting an independent
column. -/
lemma selectedProjector_insert_mulVec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {p : Fin n}
    (hp : p ∉ J) (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A (insert p J)).det ≠ 0) (x : Fin k → ℝ) :
    selectedProjector A (insert p J) *ᵥ x =
      selectedProjector A J *ᵥ x +
        ((x ⬝ᵥ residualVec A J p) * (residualSq A J p)⁻¹) •
          residualVec A J p := by
  set P := selectedProjector A J
  set w := residualVec A J p
  set δ := residualSq A J p
  have hδ : δ ≠ 0 := residualSq_ne_zero_of_insert_det A hp hG hG'
  have hw : w = A.col p - P *ᵥ A.col p := by
    simpa [w, P] using residualVec_sub A J p
  have hsub : J ⊆ insert p J := subset_insert _ _
  apply selectedProjector_mulVec_unique A hG' x
    (P *ᵥ x + ((x ⬝ᵥ w) * δ⁻¹) • w)
  · apply Submodule.add_mem
    · exact span_range_col_mono A hsub (selectedProjector_mem_span A J x)
    · apply Submodule.smul_mem
      rw [hw]
      exact Submodule.sub_mem _
        (col_mem_span_range A (mem_insert_self _ _))
        (span_range_col_mono A hsub (selectedProjector_mem_span A J _))
  · intro j hj
    have hdecomp :
        x - (P *ᵥ x + ((x ⬝ᵥ w) * δ⁻¹) • w) =
          (x - P *ᵥ x) - ((x ⬝ᵥ w) * δ⁻¹) • w := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdecomp, dotProduct_sub_eq, dotProduct_smul, smul_eq_mul]
    rcases mem_insert.mp hj with hjp | hjt
    · -- `hjp : j = p`; keep `p` in context (do not `subst`).
      have hx : x - P *ᵥ x = (1 - P) *ᵥ x := by
        rw [sub_mulVec_eq, one_mulVec_eq]
      have h1P : (1 - P)ᵀ = 1 - P := by
        rw [Matrix.transpose_sub, Matrix.transpose_one,
          selectedProjector_transpose]
      have hid : A.col j ⬝ᵥ (x - P *ᵥ x) = x ⬝ᵥ w := by
        rw [hjp, hx, ← transpose_mulVec_dot (1 - P) (A.col p) x, h1P]
        have hw' : (1 - P) *ᵥ A.col p = w := rfl
        rw [hw', dotProduct_comm]
      have hwv : A.col j ⬝ᵥ w = δ := by
        rw [hjp]
        change A.col p ⬝ᵥ residualVec A J p = residualSq A J p
        unfold residualVec
        have hcolp : A.col p = (fun i => A i p) := rfl
        rw [hcolp]
        exact (residualSq_eq_quadForm A J p hG).symm
      rw [hid, hwv, mul_assoc, inv_mul_cancel₀ hδ]
      ring
    · have hperp0 := col_dot_sub_selectedProjector A hjt hG x
      have hfix : P *ᵥ A.col j = A.col j := selectedProjector_col A hjt hG
      have hzero : A.col j ⬝ᵥ w = 0 := by
        change A.col j ⬝ᵥ residualVec A J p = 0
        unfold residualVec
        rw [← transpose_mulVec_dot (1 - P) (A.col j) (A.col p)]
        have h1P : (1 - P)ᵀ = 1 - P := by
          rw [Matrix.transpose_sub, Matrix.transpose_one,
            selectedProjector_transpose]
        rw [h1P, sub_mulVec_eq, one_mulVec_eq, hfix, sub_self, zero_dotProduct]
      rw [hperp0, hzero, mul_zero, sub_zero]

/-- Rank-1 residual downdate after inserting an independent column.
This is not a CPQR inverse-norm bound. -/
theorem residualSq_insert_downdate {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {p : Fin n}
    (hp : p ∉ J) (hG : (selectedColGram A J).det ≠ 0)
    (hG' : (selectedColGram A (insert p J)).det ≠ 0) (j : Fin n) :
    residualSq A (insert p J) j =
      residualSq A J j -
        (((fun i => A i j) ⬝ᵥ residualVec A J p) ^ 2) *
          (residualSq A J p)⁻¹ := by
  rw [residualSq_eq_quadForm A _ j hG, residualSq_eq_quadForm A _ j hG']
  have hstep :
      (1 - selectedProjector A (insert p J)) *ᵥ (fun i => A i j) =
        (1 - selectedProjector A J) *ᵥ (fun i => A i j) -
          (((fun i => A i j) ⬝ᵥ residualVec A J p) *
            (residualSq A J p)⁻¹) • residualVec A J p := by
    rw [sub_mulVec_eq, sub_mulVec_eq, one_mulVec_eq,
      selectedProjector_insert_mulVec A hp hG hG' (fun i => A i j)]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hstep, dotProduct_sub_eq, dotProduct_smul, smul_eq_mul]
  ring

/-- Residual after inserting a CPQR pivot equals the previous residual minus
the squared Gram–Schmidt coefficient. Reusable form of the inline identity
in `TriangularBound.lean`. Not a joint `poly(n, k)` bound. -/
theorem residualSq_cpqr_downdate {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {s : ℕ} (hs : s < k) (j : Fin n) :
    residualSq A (cpqrIterate A (s + 1)) j =
      residualSq A (cpqrIterate A s) j -
        ((A.col j ⬝ᵥ gsW A hA s) ^ 2) * (gsδ A hA s)⁻¹ := by
  have hp := (cpqrChosen_spec A hA hs).1
  have hins := (cpqrChosen_spec A hA hs).2.1
  have hG := gramIterate_det_ne_zero A hA s (Nat.le_of_lt hs)
  have hG' : (selectedColGram A
      (insert (cpqrChosen A hA s hs) (cpqrIterate A s))).det ≠ 0 := by
    rw [← hins]
    exact gramIterate_det_ne_zero A hA (s + 1) hs
  have hw : gsW A hA s =
      residualVec A (cpqrIterate A s) (cpqrChosen A hA s hs) := by
    rw [gsW_eq A hA hs, residualVec_eq, pivotVec_eq_col]
  have hδ : gsδ A hA s =
      residualSq A (cpqrIterate A s) (cpqrChosen A hA s hs) :=
    gsδ_eq A hA hs
  have hcol : A.col j = (fun i => A i j) := rfl
  rw [hins, hw, hδ, hcol]
  exact residualSq_insert_downdate A hp hG hG' j

end StructuredColumnSelection
