import StructuredColumnSelection.StaticClass
import StructuredColumnSelection.WideCPQRGrowth

/-!
# Normalized coherence of the outcome-2 frame is 1

The filler block repeats every completion column. Two of those copies are
equal and have positive energy, so their normalized coherence is `1`.
The same frame is the outcome-2 CPQR counterexample, so it beats every
polynomial `C (n + k + 1)^{2d}`.

Any class that requires normalized coherence strictly below `1` excludes
this frame. The theorem does not prove a polynomial bound on that class.
Absolute inner-product incoherence is a different predicate. This does
not close outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma equal_column_ratio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j1 j2 : Fin n)
    (heq : ∀ i, A i j1 = A i j2) (hpos : 0 < residualSq A ∅ j1) :
    |colInner A j1 j2| /
        (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2)) = 1 := by
  have hinner : colInner A j1 j2 = residualSq A ∅ j1 := by
    simp only [colInner, residualSq_empty]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heq i, pow_two]
  have hres : residualSq A ∅ j2 = residualSq A ∅ j1 := by
    simp only [residualSq_empty]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← heq i]
  have hden : Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2) =
      residualSq A ∅ j1 := by
    rw [hres, ← pow_two, Real.sq_sqrt (residualSq_nonneg A ∅ j1)]
  rw [hinner, hden, abs_of_pos hpos]
  exact div_self (ne_of_gt hpos)

theorem normalized_coherence_one (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        OrthogonalRows A ∧
        (∃ j1 j2 : Fin n, j1 ≠ j2 ∧ (∀ i, A i j1 = A i j2) ∧
          0 < residualSq A ∅ j1 ∧
          |colInner A j1 j2| /
            (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2)) = 1) ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x := by
  obtain ⟨m, hm, hpoly⟩ := exists_scale_beats_polynomial d hC 0
  have hm2 : 2 ≤ m := (le_max_right (0 : ℕ) 2).trans hm
  obtain ⟨A, hA, hblock, hset, _hfill, j1, j2, hjne, heq, hE⟩ :=
    wide_frame_pivots hm2
  have hkn : wideDim m ≤ wideWidth m := Nat.le_add_right _ _
  let J := widePrefix (wideWidth m) (wideDim m)
  let hcard : J.card = wideDim m := widePrefix_card hkn
  let y : Fin (wideDim m) → ℝ := wideWitness m
  let x : Fin J.card → ℝ := fun j => y (Fin.cast hcard j)
  have hcast : ∀ j : Fin (wideDim m),
      Fin.castLE hkn j = j.castAdd (wideDim m * wideRepeats m) := fun _ => rfl
  have hmul : selectedCols A J *ᵥ x = wideTriangular m *ᵥ y := by
    ext i
    simp only [Matrix.mulVec, dotProduct_eq]
    refine Fintype.sum_equiv (finCongr hcard)
      (fun j => selectedCols A J i j * x j)
      (fun j => wideTriangular m i j * y j) ?_
    intro j
    rw [selectedCols_widePrefix_apply hkn]
    rw [hcast (Fin.cast hcard j), hblock]
    simp [x, y]
  have hAx : vecEnergy (selectedCols A J *ᵥ x) = 1 := by
    rw [hmul]
    exact wideWitness_image_energy hm2
  have hx : wideGrowthLower m ^ 2 ≤ vecEnergy x := by
    rw [show vecEnergy x = vecEnergy y by
      simpa [x, y] using vecEnergy_finCast hcard y]
    exact wideWitness_energy_lower hm2
  have hpos : 0 < residualSq A ∅ j1 := by
    simpa [residualSq_empty, vecEnergy] using hE
  refine ⟨wideDim m, wideWidth m, A, ?_⟩
  rw [hset]
  refine ⟨x, hA, ?_, ?_⟩
  · exact ⟨j1, j2, hjne, heq, hpos, equal_column_ratio A j1 j2 heq hpos⟩
  · calc
      C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) *
          vecEnergy (selectedCols A J *ᵥ x)
          = C * ((wideWidth m + wideDim m + 1 : ℕ) : ℝ) ^ (2 * d) := by
            rw [hAx]
            ring
      _ < wideGrowthLower m ^ 2 := hpoly
      _ ≤ vecEnergy x := hx

end StructuredColumnSelection
