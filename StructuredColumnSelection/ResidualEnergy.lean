import StructuredColumnSelection.ColumnPivotedQR
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Residual energy of a Gram projector

If `J` is independent, the squared residuals after projecting off
`span(A_J)` sum to `k - #J` on an orthogonal-row matrix. The next
unused residual is therefore at least `(k-#J)/(n-#J)`.

This is a finite Gram-projector identity, not a CPQR inverse-norm
bound and not a polynomial theorem.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

lemma mulVec_sum_eq {k t : ℕ} (M : Matrix (Fin k) (Fin t) ℝ) (v : Fin t → ℝ)
    (i : Fin k) : (M *ᵥ v) i = ∑ j : Fin t, M i j * v j :=
  rfl

lemma dotProduct_eq {k : ℕ} (v w : Fin k → ℝ) :
    (v ⬝ᵥ w) = ∑ i : Fin k, v i * w i :=
  rfl

lemma one_mulVec_eq {k : ℕ} (v : Fin k → ℝ) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ v) = v := by
  ext i
  simp [mulVec_sum_eq, Matrix.one_apply]

lemma sub_mulVec_eq {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    ((M - N) *ᵥ v) = (M *ᵥ v) - (N *ᵥ v) := by
  ext i
  simp [mulVec_sum_eq, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma mulVec_mul_eq {k t s : ℕ}
    (M : Matrix (Fin k) (Fin t) ℝ) (N : Matrix (Fin t) (Fin s) ℝ)
    (v : Fin s → ℝ) :
    ((M * N) *ᵥ v) = M *ᵥ (N *ᵥ v) := by
  ext i
  simp only [mulVec_sum_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma dotProduct_sub_eq {k : ℕ} (v w x : Fin k → ℝ) :
    (v ⬝ᵥ (w - x)) = (v ⬝ᵥ w) - (v ⬝ᵥ x) := by
  simp only [dotProduct_eq]
  change ∑ i : Fin k, v i * (w i - x i) = ∑ i : Fin k, v i * w i - ∑ i : Fin k, v i * x i
  simp [mul_sub, Finset.sum_sub_distrib]


/-- Column-span projector `B (Bᵀ B)⁻¹ Bᵀ`. Empty `J` yields the zero
matrix. Marked `noncomputable` because of the ring inverse. -/
noncomputable def selectedProjector {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) : Matrix (Fin k) (Fin k) ℝ :=
  selectedCols A J * (selectedColGram A J)⁻¹ * (selectedCols A J)ᵀ

lemma quadForm_expand {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ) :
    (v ⬝ᵥ (M *ᵥ v)) = ∑ i : Fin k, v i * ∑ l : Fin k, M i l * v l := by
  simp only [dotProduct_eq, mulVec_sum_eq]

lemma sum_col_quadForm {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    ∑ j : Fin n, ((fun i => A i j) ⬝ᵥ (M *ᵥ fun i => A i j)) =
      (M * A * Aᵀ).trace := by
  have hRHS :
      (M * A * Aᵀ).trace =
        ∑ i : Fin k, ∑ l : Fin k, ∑ j : Fin n, M i l * A l j * A i j := by
    simp only [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (M * A * Aᵀ) i i =
        ∑ j : Fin n, (∑ l : Fin k, M i l * A l j) * A i j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine this.trans ?_
    have hswap :
        ∑ j : Fin n, (∑ l : Fin k, M i l * A l j) * A i j =
          ∑ l : Fin k, ∑ j : Fin n, M i l * A l j * A i j := by
      have h1 :
          ∑ j : Fin n, (∑ l : Fin k, M i l * A l j) * A i j =
            ∑ j : Fin n, ∑ l : Fin k, (M i l * A l j) * A i j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
      rw [h1, Finset.sum_comm]
    exact hswap
  have hLHS :
      ∑ j : Fin n, ((fun i => A i j) ⬝ᵥ (M *ᵥ fun i => A i j)) =
        ∑ i : Fin k, ∑ l : Fin k, ∑ j : Fin n, M i l * A l j * A i j := by
    simp only [quadForm_expand]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 :
        ∑ j : Fin n, A i j * ∑ l : Fin k, M i l * A l j =
          ∑ j : Fin n, ∑ l : Fin k, A i j * (M i l * A l j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact hLHS.trans hRHS.symm

lemma sum_col_quadForm_orthogonal {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    ∑ j : Fin n, ((fun i => A i j) ⬝ᵥ (M *ᵥ fun i => A i j)) = M.trace := by
  have h := sum_col_quadForm A M
  have hmul : M * A * Aᵀ = M := by
    have : A * Aᵀ = (1 : Matrix (Fin k) (Fin k) ℝ) := hA
    calc
      M * A * Aᵀ = M * (A * Aᵀ) := by rw [Matrix.mul_assoc]
      _ = M * 1 := by rw [this]
      _ = M := by simp
  simpa [hmul] using h

@[instance_reducible]
noncomputable def invertible_of_det_ne_zero {t : ℕ}
    (G : Matrix (Fin t) (Fin t) ℝ) (h : G.det ≠ 0) : Invertible G :=
  G.invertibleOfIsUnitDet (Ne.isUnit h)

lemma selectedProjector_empty {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) :
    selectedProjector A (∅ : Finset (Fin n)) = 0 := by
  ext i j
  simp only [selectedProjector, Matrix.mul_apply]
  exact Finset.sum_eq_zero fun p _ => Fin.elim0 p

lemma appendColumn_gram_castSucc {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) (p q : Fin t) :
    ((appendColumn B v)ᵀ * appendColumn B v) p.castSucc q.castSucc =
      (Bᵀ * B) p q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, appendColumn_castSucc]

lemma appendColumn_gram_castSucc_last {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) (p : Fin t) :
    ((appendColumn B v)ᵀ * appendColumn B v) p.castSucc (Fin.last t) =
      ∑ i : Fin k, B i p * v i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, appendColumn_castSucc,
    appendColumn_last]

lemma appendColumn_gram_last_castSucc {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) (q : Fin t) :
    ((appendColumn B v)ᵀ * appendColumn B v) (Fin.last t) q.castSucc =
      ∑ i : Fin k, v i * B i q := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, appendColumn_castSucc,
    appendColumn_last]

lemma appendColumn_gram_last {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) :
    ((appendColumn B v)ᵀ * appendColumn B v) (Fin.last t) (Fin.last t) =
      ∑ i : Fin k, v i * v i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, appendColumn_last]

lemma mulVec_eq_sum_transpose {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) (p : Fin t) :
    (Bᵀ *ᵥ v) p = ∑ i : Fin k, B i p * v i := by
  simp only [mulVec_sum_eq, Matrix.transpose_apply]

lemma dotProduct_self {k : ℕ} (v : Fin k → ℝ) :
    (v ⬝ᵥ v) = ∑ i : Fin k, v i * v i := by
  simp only [dotProduct_eq]

lemma castAdd_one_eq_castSucc {t : ℕ} (p : Fin t) :
    p.castAdd 1 = p.castSucc :=
  Fin.ext rfl

lemma finSumFinEquiv_inl_castSucc {t : ℕ} (p : Fin t) :
    finSumFinEquiv (Sum.inl p : Fin t ⊕ Fin 1) = p.castSucc := by
  rw [finSumFinEquiv_apply_left, castAdd_one_eq_castSucc]

lemma finSumFinEquiv_inr_last (t : ℕ) (q : Fin 1) :
    finSumFinEquiv (Sum.inr q : Fin t ⊕ Fin 1) = Fin.last t := by
  have hq : q = 0 := Subsingleton.elim _ _
  rw [hq, finSumFinEquiv_apply_right]
  exact Fin.ext (by simp [Fin.natAdd, Fin.last])

lemma appendColumn_gram_fromBlocks {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) :
    ((appendColumn B v)ᵀ * appendColumn B v).submatrix
        finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (Bᵀ * B)
        (fun p (_ : Fin 1) => (Bᵀ *ᵥ v) p)
        (fun (_ : Fin 1) q => (Bᵀ *ᵥ v) q)
        (fun (_ : Fin 1) (_ : Fin 1) => v ⬝ᵥ v) := by
  apply Matrix.ext
  rintro (p | p) (q | q)
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_inl_castSucc,
      appendColumn_gram_castSucc, Matrix.fromBlocks]
    rfl
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_inl_castSucc,
      finSumFinEquiv_inr_last, appendColumn_gram_castSucc_last,
      mulVec_eq_sum_transpose, Matrix.fromBlocks]
    rfl
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_inr_last,
      finSumFinEquiv_inl_castSucc, appendColumn_gram_last_castSucc,
      mulVec_eq_sum_transpose, Matrix.fromBlocks]
    refine Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · simp only [Matrix.submatrix_apply, finSumFinEquiv_inr_last,
      appendColumn_gram_last, dotProduct_self, Matrix.fromBlocks]
    rfl

lemma appendColumn_gram_det {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) :
    ((appendColumn B v)ᵀ * appendColumn B v).det =
      (Matrix.fromBlocks (Bᵀ * B)
        (fun p (_ : Fin 1) => (Bᵀ *ᵥ v) p)
        (fun (_ : Fin 1) q => (Bᵀ *ᵥ v) q)
        (fun (_ : Fin 1) (_ : Fin 1) => v ⬝ᵥ v)).det := by
  have h := appendColumn_gram_fromBlocks B v
  have hdet :=
    Matrix.det_submatrix_equiv_self (e := finSumFinEquiv)
      ((appendColumn B v)ᵀ * appendColumn B v)
  exact hdet.symm.trans (congrArg Matrix.det h)

lemma schur_scalar {t : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (w : Fin t → ℝ) (α : ℝ) [Invertible G] :
    (Matrix.fromBlocks G
        (fun p (_ : Fin 1) => w p)
        (fun (_ : Fin 1) q => w q)
        (fun (_ : Fin 1) (_ : Fin 1) => α)).det =
      G.det * (α - (w ⬝ᵥ (⅟G *ᵥ w))) := by
  let B : Matrix (Fin t) (Fin 1) ℝ := fun p _ => w p
  let C : Matrix (Fin 1) (Fin t) ℝ := fun _ q => w q
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => α
  have hschur := Matrix.det_fromBlocks₁₁ (A := G) (B := B) (C := C) (D := D)
  refine hschur.trans ?_
  have h1 : (D - C * ⅟G * B).det = α - (w ⬝ᵥ (⅟G *ᵥ w)) := by
    rw [Matrix.det_fin_one]
    set Ginv : Matrix (Fin t) (Fin t) ℝ := ⅟G
    have hsub : (D - C * Ginv * B) 0 0 = D 0 0 - (C * Ginv * B) 0 0 :=
      Matrix.sub_apply _ _ 0 0
    have hD : D 0 0 = α := rfl
    have hmul : (C * Ginv * B) 0 0 = w ⬝ᵥ (Ginv *ᵥ w) := by
      have hmul1 : (C * Ginv * B) 0 0 =
          ∑ q : Fin t, (∑ p : Fin t, C 0 p * Ginv p q) * B q 0 := by
        simp only [Matrix.mul_apply]
      refine hmul1.trans ?_
      have hmul2 :
          ∑ q : Fin t, (∑ p : Fin t, C 0 p * Ginv p q) * B q 0 =
            ∑ q : Fin t, ∑ p : Fin t, w p * Ginv p q * w q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        have hw :
            (∑ p : Fin t, C 0 p * Ginv p q) * B q 0 =
              (∑ p : Fin t, w p * Ginv p q) * w q := by
          simp only [C, B]
        rw [hw, Finset.sum_mul]
      refine hmul2.trans ?_
      have hmul3 :
          ∑ q : Fin t, ∑ p : Fin t, w p * Ginv p q * w q =
            ∑ p : Fin t, w p * ∑ q : Fin t, Ginv p q * w q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        have hassoc :
            ∑ q : Fin t, w p * Ginv p q * w q =
              ∑ q : Fin t, w p * (Ginv p q * w q) := by
          refine Finset.sum_congr rfl fun q _ => mul_assoc _ _ _
        rw [hassoc, ← Finset.mul_sum]
      exact hmul3.trans (by simp only [dotProduct_eq, mulVec_sum_eq])
    have hGinv : Ginv = ⅟G := rfl
    rw [hGinv] at hsub hmul
    rw [hsub, hD, hmul]
  exact congrArg (fun z => G.det * z) h1

lemma transpose_mulVec_dot {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ) (w : Fin t → ℝ) :
    ((Bᵀ *ᵥ v) ⬝ᵥ w) = (v ⬝ᵥ (B *ᵥ w)) := by
  calc
    (Bᵀ *ᵥ v) ⬝ᵥ w
        = ∑ p : Fin t, (Bᵀ *ᵥ v) p * w p := dotProduct_eq _ _
    _ = ∑ p : Fin t, (∑ i : Fin k, B i p * v i) * w p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mulVec_eq_sum_transpose]
    _ = ∑ p : Fin t, ∑ i : Fin k, B i p * v i * w p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i : Fin k, ∑ p : Fin t, v i * (B i p * w p) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ = ∑ i : Fin k, v i * ∑ p : Fin t, B i p * w p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
    _ = v ⬝ᵥ (B *ᵥ w) := by
        rw [dotProduct_eq]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mulVec_sum_eq]

lemma residual_quadForm_of_append {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ)
    (hG : (Bᵀ * B).det ≠ 0) :
    ((appendColumn B v)ᵀ * appendColumn B v).det / (Bᵀ * B).det =
      (v ⬝ᵥ ((1 - B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v)) := by
  letI := invertible_of_det_ne_zero (Bᵀ * B) hG
  have hinv : ⅟(Bᵀ * B) = (Bᵀ * B)⁻¹ := Matrix.invOf_eq_nonsing_inv (Bᵀ * B)
  have hdet := appendColumn_gram_det B v
  have hschur := schur_scalar (Bᵀ * B) (Bᵀ *ᵥ v) (v ⬝ᵥ v)
  have hdiv :
      ((appendColumn B v)ᵀ * appendColumn B v).det / (Bᵀ * B).det =
        (v ⬝ᵥ v) - ((Bᵀ *ᵥ v) ⬝ᵥ (⅟(Bᵀ * B) *ᵥ (Bᵀ *ᵥ v))) := by
    rw [hdet, hschur, mul_div_cancel_left₀ _ hG]
  refine hdiv.trans ?_
  have hproj :
      (Bᵀ *ᵥ v) ⬝ᵥ (⅟(Bᵀ * B) *ᵥ (Bᵀ *ᵥ v)) =
        v ⬝ᵥ ((B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v) := by
    have h1 := transpose_mulVec_dot B v (⅟(Bᵀ * B) *ᵥ (Bᵀ *ᵥ v))
    refine h1.trans ?_
    have h2 :
        B *ᵥ (⅟(Bᵀ * B) *ᵥ (Bᵀ *ᵥ v)) =
          (B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v := by
      rw [hinv, ← mulVec_mul_eq, ← mulVec_mul_eq, Matrix.mul_assoc]
    rw [h2]
  have hsplit :
      (v ⬝ᵥ v) - v ⬝ᵥ ((B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v) =
        v ⬝ᵥ ((1 - B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v) := by
    have hsub :
        (1 - B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v =
          v - (B * (Bᵀ * B)⁻¹ * Bᵀ) *ᵥ v := by
      rw [sub_mulVec_eq, one_mulVec_eq]
    rw [hsub, dotProduct_sub_eq]
  rw [hproj]
  exact hsplit

lemma residualSq_eq_quadForm {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n)
    (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j =
      ((fun i => A i j) ⬝ᵥ
        ((1 - selectedProjector A J) *ᵥ fun i => A i j)) := by
  by_cases h0 : J.card = 0
  · have hJ : J = ∅ := Finset.card_eq_zero.mp h0
    subst hJ
    have hP := selectedProjector_empty A
    have henergy : residualSq A ∅ j = ∑ i : Fin k, A i j ^ 2 :=
      residualSq_empty A j
    have hdot : ((fun i => A i j) ⬝ᵥ (fun i => A i j)) =
        ∑ i : Fin k, A i j ^ 2 := by
      simp only [dotProduct_eq, pow_two]
    have hone : (1 - selectedProjector A (∅ : Finset (Fin n))) *ᵥ
        (fun i => A i j) = fun i => A i j := by
      rw [hP, sub_zero, one_mulVec_eq]
    rw [henergy, hone, hdot]
  · have hres : residualSq A J j =
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det /
          (selectedColGram A J).det := by
      unfold residualSq
      simp [h0, hG]
    have hquad :=
      residual_quadForm_of_append (selectedCols A J) (fun i => A i j)
        (by simpa [selectedColGram] using hG)
    simpa [hres, selectedProjector, selectedColGram] using hquad

lemma selectedProjector_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    (selectedProjector A J).trace = (J.card : ℝ) := by
  letI := invertible_of_det_ne_zero (selectedColGram A J) hG
  have hinv : (selectedColGram A J)⁻¹ = ⅟(selectedColGram A J) :=
    (Matrix.invOf_eq_nonsing_inv (selectedColGram A J)).symm
  have hcycle :
      (selectedCols A J * (selectedColGram A J)⁻¹ *
          (selectedCols A J)ᵀ).trace =
        ((selectedColGram A J)⁻¹ * (selectedCols A J)ᵀ *
          selectedCols A J).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have hGid : (selectedColGram A J)⁻¹ * selectedColGram A J = 1 := by
    rw [hinv]
    exact invOf_mul_self _
  have hone : (selectedColGram A J)⁻¹ * (selectedCols A J)ᵀ *
      selectedCols A J = 1 := by
    simpa [selectedColGram, Matrix.mul_assoc] using hGid
  have htr : (1 : Matrix (Fin J.card) (Fin J.card) ℝ).trace = (J.card : ℝ) := by
    simp [Matrix.trace_one, Fintype.card_fin]
  simpa [selectedProjector, hone] using hcycle.trans (by simp [hone, htr])

/-- Residual energy: independent residuals sum to the complementary rank. -/
theorem residualEnergy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ∑ j : Fin n, residualSq A J j = (k : ℝ) - (J.card : ℝ) := by
  have hquad :
      ∑ j : Fin n, residualSq A J j =
        ∑ j : Fin n,
          ((fun i => A i j) ⬝ᵥ
            ((1 - selectedProjector A J) *ᵥ fun i => A i j)) :=
    Finset.sum_congr rfl fun j _ => residualSq_eq_quadForm A J j hG
  have hsum :=
    sum_col_quadForm_orthogonal A hA (1 - selectedProjector A J)
  have htr :
      (1 - selectedProjector A J).trace = (k : ℝ) - (J.card : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one, selectedProjector_trace A J hG]
    simp [Fintype.card_fin]
  exact hquad.trans (hsum.trans htr)

lemma residualSq_eq_zero_of_mem {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j = 0 := by
  have h0 : J.card ≠ 0 := by
    intro hz
    have : J = ∅ := Finset.card_eq_zero.mp hz
    subst this
    exact (notMem_empty j) hj
  have hres : residualSq A J j =
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det /
        (selectedColGram A J).det := by
    unfold residualSq
    simp [h0, hG]
  set B := selectedCols A J
  set v : Fin k → ℝ := fun i => A i j
  set B' := appendColumn B v
  have hv : A.col j = v := by
    ext i
    simp [Matrix.col, Matrix.transpose_apply, v]
  have hrange : Set.range B'.col = Set.range B.col := by
    rw [range_appendColumn_col]
    have : v ∈ Set.range B.col := by
      rw [← hv]
      exact (range_selectedCols_col A J).symm ▸ ⟨j, hj, rfl⟩
    exact Set.insert_eq_of_mem this
  have hBrank : B.rank = J.card := by
    have : (Bᵀ * B).rank = Fintype.card (Fin J.card) :=
      Matrix.rank_of_det_ne_zero (by simpa [selectedColGram] using hG)
    simpa [Matrix.rank_transpose_mul_self, Fintype.card_fin] using this
  have hB'rank : B'.rank = J.card := by
    rw [Matrix.rank_eq_finrank_span_cols, hrange,
      ← Matrix.rank_eq_finrank_span_cols, hBrank]
  have hG'det : (B'ᵀ * B').det = 0 := by
    by_contra hne
    have hrank := Matrix.rank_of_det_ne_zero hne
    have : (B'ᵀ * B').rank = J.card + 1 := by
      simpa [Fintype.card_fin] using hrank
    have : B'.rank = J.card + 1 := by
      simpa [Matrix.rank_transpose_mul_self] using this
    omega
  simp [hres, hG'det]

lemma unused_residual_sum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ∑ j ∈ unused J, residualSq A J j = (k : ℝ) - (J.card : ℝ) := by
  have henergy := residualEnergy A hA J hG
  have hdisj : Disjoint J (unused J) := disjoint_sdiff
  have hunion : J ∪ unused J = (univ : Finset (Fin n)) := by
    simp [unused, union_sdiff_of_subset (subset_univ J)]
  have hsplit :
      ∑ j : Fin n, residualSq A J j =
        ∑ j ∈ J, residualSq A J j + ∑ j ∈ unused J, residualSq A J j := by
    have := sum_union (f := residualSq A J) hdisj
    rw [hunion] at this
    exact this
  have hJ0 : ∑ j ∈ J, residualSq A J j = 0 :=
    sum_eq_zero fun j hj => residualSq_eq_zero_of_mem A hj hG
  simpa [hsplit, hJ0] using henergy

lemma unused_card {n : ℕ} (J : Finset (Fin n)) :
    (unused J).card = n - J.card := by
  simp [unused, card_sdiff, Fintype.card_fin, card_univ]

lemma orthogonalRows_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    k ≤ n := by
  have hr := orthogonalRows_rank A hA
  have hw := Matrix.rank_le_width A
  omega

/-- The largest unused residual is at least the complementary-rank average. -/
theorem nextResidual_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (hcard : J.card < n) :
    ((k : ℝ) - (J.card : ℝ)) / ((n : ℝ) - (J.card : ℝ)) ≤
      maxResidual A J := by
  have hne : (unused J).Nonempty := by
    refine card_pos.mp ?_
    have : 0 < n - J.card := Nat.sub_pos_of_lt hcard
    simpa [unused_card] using this
  have hsum := unused_residual_sum A hA J hG
  have hle : ∀ j ∈ unused J, residualSq A J j ≤ maxResidual A J :=
    fun j hj => residualSq_le_maxResidual A hne hj
  have hbound :
      ∑ j ∈ unused J, residualSq A J j ≤
        ∑ _ ∈ unused J, maxResidual A J :=
    sum_le_sum hle
  have hcardR : ((unused J).card : ℝ) = (n : ℝ) - (J.card : ℝ) := by
    have : (unused J).card = n - J.card := unused_card J
    have hle' : J.card ≤ n := le_of_lt hcard
    simp [this, Nat.cast_sub hle']
  have havg :
      (k : ℝ) - (J.card : ℝ) ≤
        ((n : ℝ) - (J.card : ℝ)) * maxResidual A J := by
    simpa [hsum, sum_const, nsmul_eq_mul, hcardR] using hbound
  have hden : (0 : ℝ) < (n : ℝ) - (J.card : ℝ) := by
    have : (0 : ℝ) < ((n - J.card : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.sub_pos_of_lt hcard)
    simpa [Nat.cast_sub (le_of_lt hcard)] using this
  exact (div_le_iff₀ hden).mpr (by rw [mul_comm]; exact havg)

end StructuredColumnSelection
