import StructuredColumnSelection.CSSPBridge
import StructuredColumnSelection.InvTraceInduction
import StructuredColumnSelection.SigmaMinBounds
import Mathlib.Analysis.Matrix.Order

/-!
# Squared spectral bound for the increment pivot

The increment pivot of `milestoneE_minimizing_inv_trace_le` selects a
`k`-column block whose Gram inverse trace is at most `k (n - k + 1)`.
Every singular value of a column submatrix of an orthogonal-row matrix
is at most `1`, so the eigenvalues of that inverse Gram are at least `1`.
The largest one is therefore at most `trace(G⁻¹) - (k - 1)`, which is at
most `1 + k (n - k)`.

The resulting inequality is `‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. It is the
square of an operator-norm bound. It is not a max-residual CPQR bound.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma selectedCols_eq_mul_colEmbed {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) :
    selectedCols A J =
      A * colEmbed (J.orderEmbOfFin rfl).toEmbedding := by
  ext i p
  rw [colEmbed_mul_apply]
  simp [selectedCols, Matrix.submatrix_apply]

lemma vecEnergy_colEmbed {n t : ℕ} (e : Fin t ↪ Fin n) (x : Fin t → ℝ) :
    vecEnergy (colEmbed e *ᵥ x) = vecEnergy x := by
  rw [vecEnergy_eq_dot, vecEnergy_eq_dot]
  have hmul : (colEmbed e)ᵀ *ᵥ (colEmbed e *ᵥ x) =
      ((colEmbed e)ᵀ * colEmbed e) *ᵥ x := (mulVec_mul_eq _ _ _).symm
  have hdot := transpose_mulVec_dot (colEmbed e) (colEmbed e *ᵥ x) x
  calc
    (colEmbed e *ᵥ x) ⬝ᵥ (colEmbed e *ᵥ x)
        = ((colEmbed e)ᵀ *ᵥ (colEmbed e *ᵥ x)) ⬝ᵥ x := hdot.symm
    _ = (((colEmbed e)ᵀ * colEmbed e) *ᵥ x) ⬝ᵥ x := by rw [hmul]
    _ = ((1 : Matrix (Fin t) (Fin t) ℝ) *ᵥ x) ⬝ᵥ x := by rw [colEmbed_orth]
    _ = x ⬝ᵥ x := by rw [one_mulVec_eq, dotProduct_comm]

lemma selectedCols_mulVec_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (x : Fin J.card → ℝ) :
    vecEnergy (selectedCols A J *ᵥ x) ≤ vecEnergy x := by
  let e : Fin J.card ↪ Fin n := (J.orderEmbOfFin rfl).toEmbedding
  have hmul : selectedCols A J *ᵥ x = A *ᵥ (colEmbed e *ᵥ x) := by
    rw [selectedCols_eq_mul_colEmbed]
    exact mulVec_mul_eq _ _ _
  calc
    vecEnergy (selectedCols A J *ᵥ x)
        = vecEnergy (A *ᵥ (colEmbed e *ᵥ x)) := by rw [hmul]
    _ ≤ vecEnergy (colEmbed e *ᵥ x) := mulVec_energy_le A hA _
    _ = vecEnergy x := vecEnergy_colEmbed e x

lemma selectedCols_transpose_mulVec_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (y : Fin k → ℝ) :
    vecEnergy ((selectedCols A J)ᵀ *ᵥ y) ≤ vecEnergy y := by
  set B := selectedCols A J
  set w := Bᵀ *ᵥ y
  have hdot : vecEnergy w = y ⬝ᵥ (B *ᵥ w) := by
    rw [vecEnergy_eq_dot]
    have h := transpose_mulVec_dot B y w
    simpa [w] using h
  have hcs := energy_cauchy y (B *ᵥ w)
  have hBle := selectedCols_mulVec_energy_le A hA J w
  have hsq : (vecEnergy w) ^ 2 ≤ vecEnergy y * vecEnergy w := by
    have h1 : (y ⬝ᵥ (B *ᵥ w)) ^ 2 ≤ vecEnergy y * vecEnergy (B *ᵥ w) := hcs
    rw [← hdot] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hBle (vecEnergy_nonneg y))
  by_cases h0 : vecEnergy w = 0
  · rw [h0]
    exact vecEnergy_nonneg y
  · have hpos : 0 < vecEnergy w := lt_of_le_of_ne (vecEnergy_nonneg _) (Ne.symm h0)
    have : vecEnergy w * vecEnergy w ≤ vecEnergy y * vecEnergy w := by
      simpa [pow_two] using hsq
    exact le_of_mul_le_mul_right this hpos

lemma gram_inv_quad_ge_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (x : Fin J.card → ℝ) :
    vecEnergy x ≤ x ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ x) := by
  set B := selectedCols A J
  set G := selectedColGram A J
  set z := G⁻¹ *ᵥ x
  have hGz : G *ᵥ z = x := by
    have h1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hG)
    calc
      G *ᵥ z = (G * G⁻¹) *ᵥ x := (mulVec_mul_eq _ _ _).symm
      _ = (1 : Matrix (Fin J.card) (Fin J.card) ℝ) *ᵥ x := by rw [h1]
      _ = x := one_mulVec_eq _
  have hBtz : Bᵀ *ᵥ (B *ᵥ z) = x := by
    rw [← hGz]
    simp only [G, selectedColGram, B]
    exact (mulVec_mul_eq _ _ _).symm
  have hdual := selectedCols_transpose_mulVec_energy_le A hA J (B *ᵥ z)
  have hquad : x ⬝ᵥ (G⁻¹ *ᵥ x) = vecEnergy (B *ᵥ z) := by
    have hsym : Gᵀ = G := selectedColGram_isSymm A J
    have henergy : z ⬝ᵥ (G *ᵥ z) = vecEnergy (B *ᵥ z) := by
      have := vecEnergy_selectedCols A J z
      simpa [B, G] using this.symm
    calc
      x ⬝ᵥ (G⁻¹ *ᵥ x) = x ⬝ᵥ z := by simp [z]
      _ = z ⬝ᵥ x := dotProduct_comm _ _
      _ = z ⬝ᵥ (G *ᵥ z) := by rw [hGz]
      _ = vecEnergy (B *ᵥ z) := henergy
  calc
    vecEnergy x = vecEnergy (Bᵀ *ᵥ (B *ᵥ z)) := by rw [hBtz]
    _ ≤ vecEnergy (B *ᵥ z) := hdual
    _ = x ⬝ᵥ (G⁻¹ *ᵥ x) := hquad.symm

lemma gram_inv_sub_one_posSemidef {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGram A J)⁻¹ - 1).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · change ((selectedColGram A J)⁻¹ - 1)ᴴ = (selectedColGram A J)⁻¹ - 1
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    have hinv : ((selectedColGram A J)⁻¹)ᵀ = (selectedColGram A J)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, selectedColGram_isSymm A J]
    have hstar : ((selectedColGram A J)⁻¹)ᴴ = ((selectedColGram A J)⁻¹)ᵀ := by
      ext i j
      simp
    rw [hstar, hinv]
  · intro x
    have hge := gram_inv_quad_ge_energy A hA J hG x
    simpa only [star_trivial, sub_mulVec_eq, one_mulVec_eq, dotProduct_sub_eq,
      ← vecEnergy_eq_dot] using sub_nonneg.mpr hge

lemma gram_inv_shifted_nonneg {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    0 ≤ ((selectedColGram A J)⁻¹).trace - (J.card : ℝ) + 1 := by
  have htrnn := (gram_inv_sub_one_posSemidef A hA J hG).trace_nonneg
  have htr : ((selectedColGram A J)⁻¹ - 1).trace =
      ((selectedColGram A J)⁻¹).trace - (J.card : ℝ) := by
    rw [Matrix.trace_sub, Matrix.trace_one]
    simp [Fintype.card_fin]
  rw [htr] at htrnn
  linarith

open scoped MatrixOrder in
lemma gram_inv_quad_le_shifted_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (x : Fin J.card → ℝ) :
    x ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ x) ≤
      (((selectedColGram A J)⁻¹).trace - (J.card : ℝ) + 1) * vecEnergy x := by
  set G := selectedColGram A J
  have hpsd : (G⁻¹ - 1).PosSemidef := gram_inv_sub_one_posSemidef A hA J hG
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  have hstar : star C = Cᵀ := by
    ext i j
    rfl
  have hCC : Cᵀ * C = G⁻¹ - 1 := by simpa only [hstar] using hC.symm
  have hquadM : x ⬝ᵥ ((G⁻¹ - 1) *ᵥ x) = vecEnergy (C *ᵥ x) := by
    rw [← hCC, vecEnergy_eq_dot]
    have hmul : Cᵀ *ᵥ (C *ᵥ x) = (Cᵀ * C) *ᵥ x := (mulVec_mul_eq _ _ _).symm
    have hdot := transpose_mulVec_dot C (C *ᵥ x) x
    calc
      x ⬝ᵥ ((Cᵀ * C) *ᵥ x) = ((Cᵀ * C) *ᵥ x) ⬝ᵥ x := dotProduct_comm _ _
      _ = (Cᵀ *ᵥ (C *ᵥ x)) ⬝ᵥ x := by rw [hmul]
      _ = (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := hdot
  have hle := vecEnergy_mulVec_le_frob C x
  have hMle : x ⬝ᵥ ((G⁻¹ - 1) *ᵥ x) ≤
      (G⁻¹.trace - (J.card : ℝ)) * vecEnergy x := by
    rw [← hquadM, hCC, Matrix.trace_sub, Matrix.trace_one] at hle
    simpa [Fintype.card_fin, G] using hle
  have hsplit : x ⬝ᵥ (G⁻¹ *ᵥ x) =
      x ⬝ᵥ ((G⁻¹ - 1) *ᵥ x) + vecEnergy x := by
    have hdiff : x ⬝ᵥ (G⁻¹ *ᵥ x) - vecEnergy x = x ⬝ᵥ ((G⁻¹ - 1) *ᵥ x) := by
      rw [sub_mulVec_eq, one_mulVec_eq, dotProduct_sub_eq, vecEnergy_eq_dot]
    exact (sub_eq_iff_eq_add).mp hdiff
  calc
    x ⬝ᵥ (G⁻¹ *ᵥ x) = x ⬝ᵥ ((G⁻¹ - 1) *ᵥ x) + vecEnergy x := hsplit
    _ ≤ (G⁻¹.trace - (J.card : ℝ)) * vecEnergy x + vecEnergy x :=
      add_le_add_left hMle _
    _ = (G⁻¹.trace - (J.card : ℝ) + 1) * vecEnergy x := by ring

lemma selectedCols_energy_le_shifted_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (x : Fin J.card → ℝ) :
    vecEnergy x ≤
      vecEnergy (selectedCols A J *ᵥ x) *
        (((selectedColGram A J)⁻¹).trace - (J.card : ℝ) + 1) := by
  set B := selectedCols A J
  set G := selectedColGram A J
  set y := G⁻¹ *ᵥ x
  have hGid : G *ᵥ y = x := by
    have h1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hG)
    calc
      G *ᵥ y = (G * G⁻¹) *ᵥ x := (mulVec_mul_eq _ _ _).symm
      _ = (1 : Matrix (Fin J.card) (Fin J.card) ℝ) *ᵥ x := by rw [h1]
      _ = x := one_mulVec_eq _
  have hdot : (B *ᵥ x) ⬝ᵥ (B *ᵥ y) = vecEnergy x := by
    have hmul : Bᵀ *ᵥ (B *ᵥ x) = G *ᵥ x := by
      simp only [G, selectedColGram, B]
      exact (mulVec_mul_eq _ _ _).symm
    have h1 := transpose_mulVec_dot B (B *ᵥ x) y
    have h2 : (B *ᵥ x) ⬝ᵥ (B *ᵥ y) = (G *ᵥ x) ⬝ᵥ y := by
      have : (Bᵀ *ᵥ (B *ᵥ x)) ⬝ᵥ y = (B *ᵥ x) ⬝ᵥ (B *ᵥ y) := h1
      simpa [hmul] using this.symm
    have h3 : (G *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (G *ᵥ y) := by
      have hsym : Gᵀ = G := selectedColGram_isSymm A J
      have := transpose_mulVec_dot G x y
      simpa [hsym] using this
    rw [h2, h3, hGid, vecEnergy_eq_dot]
  have hyenergy : vecEnergy (B *ᵥ y) = x ⬝ᵥ (G⁻¹ *ᵥ x) := by
    have := vecEnergy_selectedCols A J y
    rw [this, hGid]
    exact dotProduct_comm _ _
  have hCS : (vecEnergy x) ^ 2 ≤
      vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) := by
    have := energy_cauchy (B *ᵥ x) (B *ᵥ y)
    simpa [hdot, hyenergy] using this
  have hquad := gram_inv_quad_le_shifted_trace A hA J hG x
  have hcoeff : 0 ≤ G⁻¹.trace - (J.card : ℝ) + 1 :=
    gram_inv_shifted_nonneg A hA J hG
  have hbnn : 0 ≤ vecEnergy (B *ᵥ x) := vecEnergy_nonneg _
  by_cases hx0 : vecEnergy x = 0
  · simp [hx0]
    exact mul_nonneg hbnn hcoeff
  · have hxpos : 0 < vecEnergy x := lt_of_le_of_ne (vecEnergy_nonneg _) (Ne.symm hx0)
    have h1 : vecEnergy x * vecEnergy x ≤
        vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) := by
      simpa [pow_two] using hCS
    have h2 : vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) ≤
        vecEnergy (B *ᵥ x) *
          ((G⁻¹.trace - (J.card : ℝ) + 1) * vecEnergy x) :=
      mul_le_mul_of_nonneg_left (by simpa [G] using hquad) hbnn
    have h3 : vecEnergy x * vecEnergy x ≤
        (vecEnergy (B *ᵥ x) * (G⁻¹.trace - (J.card : ℝ) + 1)) * vecEnergy x := by
      have := h1.trans h2
      linarith
    exact le_of_mul_le_mul_right h3 hxpos

/-- Some `k` columns chosen by the increment bound satisfy
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

This is the square of the operator-norm bound. It is not a bound for the
max-residual CPQR pivot and does not close outcome 3. -/
theorem minimizing_inv_spectral_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ∀ x : Fin J.card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A J *ᵥ x) := by
  obtain ⟨J, hcard, hG, hf⟩ := minimizing_inv_trace_le A hA
  refine ⟨J, hcard, hG, ?_⟩
  intro x
  have henergy := selectedCols_energy_le_shifted_trace A hA J hG x
  have hshift : ((selectedColGram A J)⁻¹).trace - (J.card : ℝ) + 1 ≤
      1 + (k : ℝ) * ((n : ℝ) - k) := by
    have hcast : (J.card : ℝ) = (k : ℝ) := congrArg Nat.cast hcard
    rw [hcast]
    linarith
  have hBx : 0 ≤ vecEnergy (selectedCols A J *ᵥ x) := vecEnergy_nonneg _
  have hscaled : vecEnergy (selectedCols A J *ᵥ x) *
      (((selectedColGram A J)⁻¹).trace - (J.card : ℝ) + 1) ≤
      vecEnergy (selectedCols A J *ᵥ x) * (1 + (k : ℝ) * ((n : ℝ) - k)) :=
    mul_le_mul_of_nonneg_left hshift hBx
  have hcomm : vecEnergy (selectedCols A J *ᵥ x) *
      (1 + (k : ℝ) * ((n : ℝ) - k)) =
      (1 + (k : ℝ) * ((n : ℝ) - k)) * vecEnergy (selectedCols A J *ᵥ x) :=
    mul_comm _ _
  exact henergy.trans (hscaled.trans (le_of_eq hcomm))

end StructuredColumnSelection
