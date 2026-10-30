import StructuredColumnSelection.WideCPQRGrowth

/-!
# Design-padded adverse family

The outcome-2 frame pads the triangular block with a filler block that
repeats every completion column. The CPQR prefix argument only needs
every filler energy below the smallest squared diagonal. This file
replaces the repeat by an arbitrary tight design `W` with `W Wᵀ = 1`:
the filler block is `C W` for any completion `R Rᵀ + C Cᵀ = 1`.

The repeated frame is the design `(1/√t)[I ⋯ I]`. Nothing here bounds
the normalized coherence of the resulting columns. This does not close
outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset
open scoped Matrix

/-- Leading block `R`, then the filler block `C * W`. -/
noncomputable def designFrame {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) : Matrix (Fin k) (Fin (k + N)) ℝ :=
  fun i j => Fin.addCases (fun q => R i q) (fun q => (C * W) i q) j

lemma designFrame_left {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (i j : Fin k) :
    designFrame R C W i (j.castAdd N) = R i j := by
  simp [designFrame]

lemma designFrame_right {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (i : Fin k) (j : Fin N) :
    designFrame R C W i (j.natAdd k) = (C * W) i j := by
  simp [designFrame]

lemma designFrame_mul_transpose {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (hW : W * Wᵀ = 1) :
    designFrame R C W * (designFrame R C W)ᵀ = R * Rᵀ + C * Cᵀ := by
  have hCW : (C * W) * (C * W)ᵀ = C * Cᵀ := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W, hW,
      Matrix.one_mul]
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
  rw [Fin.sum_univ_add]
  simp only [designFrame_left, designFrame_right]
  congr 1
  have hij := congrFun (congrFun hCW i) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply] using hij

lemma designFrame_right_col {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (j : Fin N) :
    (fun i => designFrame R C W i (j.natAdd k)) = C *ᵥ (fun q => W q j) := by
  ext i
  rw [designFrame_right]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma designFrame_right_energy_le {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (W : Matrix (Fin k) (Fin N) ℝ) (j : Fin N) :
    vecEnergy (fun i => designFrame R C W i (j.natAdd k)) ≤
      frobEnergy C * vecEnergy (fun q => W q j) := by
  rw [designFrame_right_col]
  exact mulVec_energy_le_frob C _

lemma frobEnergy_add_of_completion {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hCC : R * Rᵀ + C * Cᵀ = 1) :
    frobEnergy R + frobEnergy C = (k : ℝ) := by
  have htr := congrArg Matrix.trace hCC
  simpa only [Matrix.trace_add, ← frobEnergy_eq_trace, Matrix.trace_one,
    Fintype.card_fin] using htr

/-- Any completion and any tight design give a Parseval frame whose filler
energies are controlled by the design columns. -/
theorem design_completion_orthogonal {k N : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (hCC : R * Rᵀ + C * Cᵀ = 1) (W : Matrix (Fin k) (Fin N) ℝ)
    (hW : W * Wᵀ = 1) :
    OrthogonalRows (designFrame R C W) ∧
      (∀ i j : Fin k, designFrame R C W i (j.castAdd N) = R i j) ∧
      (∀ (i : Fin k) (j : Fin N), designFrame R C W i (j.natAdd k) = (C * W) i j) ∧
      ∀ j : Fin N, vecEnergy (fun i => designFrame R C W i (j.natAdd k)) ≤
        (k : ℝ) * vecEnergy (fun q => W q j) := by
  refine ⟨(designFrame_mul_transpose R C W hW).trans hCC, designFrame_left R C W,
    designFrame_right R C W, ?_⟩
  intro j
  have hfrob : frobEnergy C ≤ (k : ℝ) := by
    have := frobEnergy_add_of_completion R C hCC
    linarith [frobEnergy_nonneg R]
  exact (designFrame_right_energy_le R C W j).trans
    (mul_le_mul_of_nonneg_right hfrob (vecEnergy_nonneg _))

/-- With the triangular leading block and a design whose columns are at most
`1 / wideRepeats m` in energy, CPQR takes the leading prefix. -/
theorem wide_design_pivots {m : ℕ} (hm : 2 ≤ m) {N : ℕ}
    (C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ)
    (hCC : wideTriangular m * (wideTriangular m)ᵀ + C * Cᵀ = 1)
    (W : Matrix (Fin (wideDim m)) (Fin N) ℝ) (hW : W * Wᵀ = 1)
    (hcol : ∀ j : Fin N, vecEnergy (fun q => W q j) ≤ 1 / (wideRepeats m : ℝ)) :
    OrthogonalRows (designFrame (wideTriangular m) C W) ∧
      cpqrSet (designFrame (wideTriangular m) C W) =
        widePrefix (wideDim m + N) (wideDim m) := by
  obtain ⟨hA, hR, _hF, hE⟩ := design_completion_orthogonal (wideTriangular m) C hCC W hW
  set A := designFrame (wideTriangular m) C W with hAdef
  have hkn : wideDim m ≤ wideDim m + N := Nat.le_add_right _ _
  have hcast (j : Fin (wideDim m)) : Fin.castLE hkn j = j.castAdd N := by rfl
  have hupper : ∀ i j : Fin (wideDim m), (j : ℕ) < (i : ℕ) →
      A i (Fin.castLE hkn j) = 0 := by
    intro i j h
    rw [hcast, hR]
    exact wideTriangular_upper h
  have hdiag : ∀ i : Fin (wideDim m), A i (Fin.castLE hkn i) ≠ 0 := by
    intro i
    rw [hcast, hR, wideTriangular_diag]
    exact (wideDiag_pos hm i).ne'
  have hfill : ∀ q : Fin N, vecEnergy (fun i => A i (q.natAdd (wideDim m))) ≤
      (wideDim m : ℝ) / (wideRepeats m : ℝ) := by
    intro q
    have hk0 : (0 : ℝ) ≤ wideDim m := by positivity
    calc vecEnergy (fun i => A i (q.natAdd (wideDim m)))
        ≤ (wideDim m : ℝ) * vecEnergy (fun r => W r q) := hE q
      _ ≤ (wideDim m : ℝ) * (1 / (wideRepeats m : ℝ)) :=
        mul_le_mul_of_nonneg_left (hcol q) hk0
      _ = (wideDim m : ℝ) / (wideRepeats m : ℝ) := mul_one_div _ _
  have htail : ∀ p : Fin (wideDim m), ∀ j : Fin (wideDim m + N),
      (p : ℕ) < (j : ℕ) → tailEnergy p (A.col j) < A p (Fin.castLE hkn p) ^ 2 := by
    intro p j hpj
    rw [hcast, hR, wideTriangular_diag]
    by_cases hj : (j : ℕ) < wideDim m
    · let q : Fin (wideDim m) := ⟨j, hj⟩
      have hjq : j = q.castAdd N := by
        ext
        simp [q]
      have hpq : (p : ℕ) < (q : ℕ) := by
        have : (j : ℕ) = (q : ℕ) := by simp [hjq]
        omega
      have hcol' : A.col j = (wideTriangular m).col q := by
        ext i
        rw [hjq]
        exact hR i q
      rw [hcol']
      exact wideTriangular_tail_lt hm p q hpq
    · have hge : wideDim m ≤ (j : ℕ) := Nat.le_of_not_lt hj
      let q : Fin N := ⟨(j : ℕ) - wideDim m, by
        have hjlt : (j : ℕ) < wideDim m + N := j.isLt
        omega⟩
      have hjq : j = q.natAdd (wideDim m) := by
        ext
        simp [q, Nat.add_sub_of_le hge]
      rw [hjq]
      exact (tailEnergy_le_energy p _).trans_lt
        ((hfill q).trans_lt (wide_filler_lt_diag hm p))
  exact ⟨hA, triangular_prefix_pivots hkn A hupper hdiag htail (wideDim m) (Nat.le_refl _)⟩

/-- The design-padded adverse family: for every completion and every tight
design with small columns, the frame has orthogonal rows, the triangular
leading block, the filler block `C W`, the literal CPQR prefix, image energy
`1`, and inverse energy at least `wideGrowthLower m ^ 2`. -/
theorem wide_design_adverse_family {m : ℕ} (hm : 2 ≤ m) {N : ℕ}
    (C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ)
    (hCC : wideTriangular m * (wideTriangular m)ᵀ + C * Cᵀ = 1)
    (W : Matrix (Fin (wideDim m)) (Fin N) ℝ) (hW : W * Wᵀ = 1)
    (hcol : ∀ j : Fin N, vecEnergy (fun q => W q j) ≤ 1 / (wideRepeats m : ℝ)) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + N)) ℝ,
      ∃ x : Fin (widePrefix (wideDim m + N) (wideDim m)).card → ℝ,
        OrthogonalRows A ∧
        (∀ i j : Fin (wideDim m), A i (j.castAdd N) = wideTriangular m i j) ∧
        (∀ (i : Fin (wideDim m)) (j : Fin N),
          A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
        cpqrSet A = widePrefix (wideDim m + N) (wideDim m) ∧
        vecEnergy (selectedCols A (widePrefix (wideDim m + N) (wideDim m)) *ᵥ x) = 1 ∧
        wideGrowthLower m ^ 2 ≤ vecEnergy x := by
  obtain ⟨hA, hset⟩ := wide_design_pivots hm C hCC W hW hcol
  set A := designFrame (wideTriangular m) C W with hAdef
  have hR : ∀ i j : Fin (wideDim m), A i (j.castAdd N) = wideTriangular m i j :=
    designFrame_left (wideTriangular m) C W
  have hkn : wideDim m ≤ wideDim m + N := Nat.le_add_right _ _
  let J := widePrefix (wideDim m + N) (wideDim m)
  let hcard : J.card = wideDim m := widePrefix_card hkn
  let y : Fin (wideDim m) → ℝ := wideWitness m
  let x : Fin J.card → ℝ := fun j => y (Fin.cast hcard j)
  have hcast : ∀ j : Fin (wideDim m), Fin.castLE hkn j = j.castAdd N := fun _ => rfl
  have hmul : selectedCols A J *ᵥ x = wideTriangular m *ᵥ y := by
    ext i
    simp only [Matrix.mulVec, dotProduct_eq]
    refine Fintype.sum_equiv (finCongr hcard)
      (fun j => selectedCols A J i j * x j)
      (fun j => wideTriangular m i j * y j) ?_
    intro j
    rw [selectedCols_widePrefix_apply hkn]
    rw [hcast (Fin.cast hcard j), hR]
    simp [x, y]
  refine ⟨A, x, hA, hR, designFrame_right (wideTriangular m) C W, hset, ?_, ?_⟩
  · rw [hmul]
    exact wideWitness_image_energy hm
  · rw [show vecEnergy x = vecEnergy y by
      simpa [x, y] using vecEnergy_finCast hcard y]
    exact wideWitness_energy_lower hm

end StructuredColumnSelection
