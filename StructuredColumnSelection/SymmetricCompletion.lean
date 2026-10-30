import StructuredColumnSelection.WideCPQR

/-!
# Symmetric completion with contraction and perturbation bounds

For `‖R‖_F² ≤ 1` the symmetric positive semidefinite square root
`C = (1 - R Rᵀ)^{1/2}` completes `R` to a Parseval frame, and `C` acts
almost like the identity:

* `⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`;
* `(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`;
* `‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`.

The perturbation bound uses `(C + I)(C - I) = -R Rᵀ` and
`‖(C + I) u‖² ≥ ‖u‖²` for `C ⪰ 0`. No coherence bound on any frame is
proved here. This does not close outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset
open scoped Matrix

lemma symmetric_completion_inner {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hsym : Cᵀ = C) (hCC : C * C = 1 - R * Rᵀ) (w v : Fin k → ℝ) :
    (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - (Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v) := by
  have h1 : (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ ((C * C) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec]
    have h0 : C *ᵥ w = Cᵀ *ᵥ w := by rw [hsym]
    rw [h0]
    exact transpose_mulVec_dot C w (C *ᵥ v)
  have h2 : w ⬝ᵥ ((R * Rᵀ) *ᵥ v) = (Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec]
    exact (transpose_mulVec_dot R w (Rᵀ *ᵥ v)).symm
  rw [h1, hCC, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h2]

lemma symmetric_completion_energy {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hsym : Cᵀ = C) (hCC : C * C = 1 - R * Rᵀ) (w : Fin k → ℝ) :
    vecEnergy (C *ᵥ w) = vecEnergy w - vecEnergy (Rᵀ *ᵥ w) := by
  rw [vecEnergy_eq_dot, vecEnergy_eq_dot, vecEnergy_eq_dot]
  exact symmetric_completion_inner R C hsym hCC w w

lemma symmetric_completion_energy_le {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hsym : Cᵀ = C) (hCC : C * C = 1 - R * Rᵀ) (w : Fin k → ℝ) :
    vecEnergy (C *ᵥ w) ≤ vecEnergy w := by
  rw [symmetric_completion_energy R C hsym hCC]
  linarith [vecEnergy_nonneg (Rᵀ *ᵥ w)]

lemma symmetric_completion_energy_ge {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hsym : Cᵀ = C) (hCC : C * C = 1 - R * Rᵀ) (w : Fin k → ℝ) :
    (1 - frobEnergy R) * vecEnergy w ≤ vecEnergy (C *ᵥ w) := by
  rw [symmetric_completion_energy R C hsym hCC]
  have h := mulVec_energy_le_frob Rᵀ w
  rw [frobEnergy_transpose] at h
  have hexp : (1 - frobEnergy R) * vecEnergy w =
      vecEnergy w - frobEnergy R * vecEnergy w := by ring
  rw [hexp]
  linarith

lemma symmetric_completion_perturb {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hsym : Cᵀ = C) (hCC : C * C = 1 - R * Rᵀ) (hpsd : C.PosSemidef)
    (v : Fin k → ℝ) :
    vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy R ^ 2 * vecEnergy v := by
  have _hsym := hsym
  set u := (C - 1) *ᵥ v with hu
  have hprod : (C + 1) * (C - 1) = -(R * Rᵀ) := by
    simp only [add_mul, mul_sub, mul_one, one_mul, hCC]
    abel
  have hCu : (C + 1) *ᵥ u = -((R * Rᵀ) *ᵥ v) := by
    rw [hu, Matrix.mulVec_mulVec, hprod, Matrix.neg_mulVec]
  have hlow : vecEnergy u ≤ vecEnergy ((C + 1) *ᵥ u) := by
    have hpos : 0 ≤ u ⬝ᵥ (C *ᵥ u) := by
      have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 u
      simpa using this
    rw [Matrix.add_mulVec, Matrix.one_mulVec, vecEnergy_eq_dot, vecEnergy_eq_dot]
    have hexp : (C *ᵥ u + u) ⬝ᵥ (C *ᵥ u + u) =
        (C *ᵥ u) ⬝ᵥ (C *ᵥ u) + 2 * (u ⬝ᵥ (C *ᵥ u)) + u ⬝ᵥ u := by
      simp only [dotProduct_add, add_dotProduct, dotProduct_comm (C *ᵥ u) u]
      ring
    rw [hexp]
    have hCuE := vecEnergy_nonneg (C *ᵥ u)
    rw [vecEnergy_eq_dot] at hCuE
    linarith
  have hup : vecEnergy ((C + 1) *ᵥ u) ≤ frobEnergy R ^ 2 * vecEnergy v := by
    rw [hCu, ← Matrix.mulVec_mulVec]
    have hneg : vecEnergy (-(R *ᵥ (Rᵀ *ᵥ v))) = vecEnergy (R *ᵥ (Rᵀ *ᵥ v)) := by
      simp [vecEnergy]
    rw [hneg]
    have h1 := mulVec_energy_le_frob R (Rᵀ *ᵥ v)
    have h2 := mulVec_energy_le_frob Rᵀ v
    rw [frobEnergy_transpose] at h2
    have hf := frobEnergy_nonneg R
    calc vecEnergy (R *ᵥ (Rᵀ *ᵥ v))
        ≤ frobEnergy R * vecEnergy (Rᵀ *ᵥ v) := h1
      _ ≤ frobEnergy R * (frobEnergy R * vecEnergy v) :=
        mul_le_mul_of_nonneg_left h2 hf
      _ = frobEnergy R ^ 2 * vecEnergy v := by ring
  exact hlow.trans hup

open scoped MatrixOrder in
/-- The symmetric positive semidefinite square root of `1 - R Rᵀ`. -/
theorem exists_symmetric_completion {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) :
    ∃ C : Matrix (Fin k) (Fin k) ℝ, Cᵀ = C ∧ C * C = 1 - R * Rᵀ ∧ C.PosSemidef := by
  have hP := complement_posSemidef R hR
  have hsqrt : (CFC.sqrt (1 - R * Rᵀ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - R * Rᵀ))
  refine ⟨CFC.sqrt (1 - R * Rᵀ), ?_, CFC.sqrt_mul_sqrt_self _ hP.nonneg, hsqrt⟩
  have hH : (CFC.sqrt (1 - R * Rᵀ))ᴴ = CFC.sqrt (1 - R * Rᵀ) := hsqrt.1
  ext i j
  have hij := congrFun (congrFun hH i) j
  simpa [Matrix.conjTranspose_apply] using hij

/-- A symmetric completion with the inner-product identity, the energy
sandwich, and the perturbation bound. -/
theorem symmetric_completion {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) :
    ∃ C : Matrix (Fin k) (Fin k) ℝ,
      Cᵀ = C ∧ R * Rᵀ + C * Cᵀ = 1 ∧
      (∀ w v : Fin k → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - (Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v)) ∧
      (∀ w : Fin k → ℝ,
        (1 - frobEnergy R) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      ∀ v : Fin k → ℝ, vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy R ^ 2 * vecEnergy v := by
  obtain ⟨C, hsym, hCC, hpsd⟩ := exists_symmetric_completion R hR
  refine ⟨C, hsym, ?_, fun w v => symmetric_completion_inner R C hsym hCC w v,
    fun w => ⟨symmetric_completion_energy_ge R C hsym hCC w,
      symmetric_completion_energy_le R C hsym hCC w⟩,
    fun v => symmetric_completion_perturb R C hsym hCC hpsd v⟩
  rw [hsym, hCC]
  abel

end StructuredColumnSelection
