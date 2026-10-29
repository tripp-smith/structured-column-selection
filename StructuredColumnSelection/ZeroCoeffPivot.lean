import StructuredColumnSelection.IncrementSet

/-!
# Zero coefficient, same pivot

If every unused column with positive residual is orthogonal to the selected
block, the inverse-trace increment is the reciprocal of the residual. The
least-index minimizer of that ratio is then the least-index maximizer of
the residual, so the increment pivot and max-residual CPQR return the same
column.

The `2×5` frame of `milestoneE_increment_set_ne_cpqr` shows that a nonzero
coefficient can separate the two rules. This lemma does not close outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma incrementRatio_of_zero_coeff {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n)
    (hzero :
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0) :
    incrementRatio A J j = 1 / residualSq A J j := by
  unfold incrementRatio
  rw [hzero, add_zero]

lemma maxResidual_eq_candidate_sup {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hs : (incrementCandidates A J).Nonempty) :
    maxResidual A J =
      (incrementCandidates A J).sup' hs (residualSq A J) := by
  have hunused : (unused J).Nonempty := by
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, (mem_filter.mp hj).1⟩
  unfold maxResidual
  rw [dif_pos hunused]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j hj
    by_cases hpos : 0 < residualSq A J j
    · rw [le_sup'_iff]
      exact ⟨j, mem_filter.mpr ⟨hj, hpos⟩, le_rfl⟩
    · rw [le_sup'_iff]
      obtain ⟨j0, hj0⟩ := hs
      have hpos0 : 0 < residualSq A J j0 := (mem_filter.mp hj0).2
      exact ⟨j0, hj0, (le_of_not_gt hpos).trans hpos0.le⟩
  · rw [sup'_le_iff]
    intro j hj
    rw [le_sup'_iff]
    exact ⟨j, (mem_filter.mp hj).1, le_rfl⟩

lemma incrementBest_eq_inv_max {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hzero : ∀ j ∈ incrementCandidates A J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0)
    (hs : (incrementCandidates A J).Nonempty) :
    incrementBest A J = 1 / maxResidual A J := by
  have hmax := maxResidual_eq_candidate_sup A J hs
  unfold incrementBest
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · obtain ⟨j, hj, hjsup⟩ :=
      Finset.exists_mem_eq_sup' hs (residualSq A J)
    have hres : residualSq A J j = maxResidual A J := by
      rw [← hjsup, hmax]
    have hratio : incrementRatio A J j = 1 / maxResidual A J := by
      rw [incrementRatio_of_zero_coeff A J j (hzero j hj), hres]
    rw [← hratio]
    exact mem_image_of_mem _ hj
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hr
    rw [incrementRatio_of_zero_coeff A J j (hzero j hj)]
    have hpos : 0 < residualSq A J j := (mem_filter.mp hj).2
    have hle : residualSq A J j ≤ maxResidual A J := by
      rw [hmax, le_sup'_iff]
      exact ⟨j, hj, le_rfl⟩
    have hmaxpos : 0 < maxResidual A J := lt_of_lt_of_le hpos hle
    simpa [one_div] using (inv_le_inv₀ hmaxpos hpos).2 hle

lemma zero_coeff_filters_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hzero : ∀ j ∈ incrementCandidates A J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0) :
    (incrementCandidates A J).filter (fun j =>
        incrementRatio A J j = incrementBest A J) =
      (unused J).filter (fun j =>
        residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j) := by
  by_cases hs : (incrementCandidates A J).Nonempty
  · ext j
    have hbest := incrementBest_eq_inv_max A J hzero hs
    constructor
    · intro hj
      have hmem := (mem_filter.mp hj).1
      have hr := (mem_filter.mp hj).2
      have hpos : 0 < residualSq A J j := (mem_filter.mp hmem).2
      have hratio := incrementRatio_of_zero_coeff A J j (hzero j hmem)
      have heq : (residualSq A J j)⁻¹ = (maxResidual A J)⁻¹ := by
        have hdiv : 1 / residualSq A J j = 1 / maxResidual A J := by
          rw [← hratio, hr, hbest]
        simpa [one_div] using hdiv
      have hres : residualSq A J j = maxResidual A J := by
        rw [← inv_inv (residualSq A J j), heq, inv_inv]
      exact mem_filter.mpr ⟨(mem_filter.mp hmem).1, hres, hpos⟩
    · intro hj
      have hunused := (mem_filter.mp hj).1
      have hres := (mem_filter.mp hj).2.1
      have hpos := (mem_filter.mp hj).2.2
      have hmem : j ∈ incrementCandidates A J := mem_filter.mpr ⟨hunused, hpos⟩
      have hratio := incrementRatio_of_zero_coeff A J j (hzero j hmem)
      refine mem_filter.mpr ⟨hmem, ?_⟩
      rw [hratio, hbest, hres]
  · have hempty : incrementCandidates A J = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [hempty, filter_empty]
    symm
    refine eq_empty_of_forall_notMem ?_
    intro j hj
    have hpos := (mem_filter.mp hj).2.2
    have hmem : j ∈ incrementCandidates A J :=
      mem_filter.mpr ⟨(mem_filter.mp hj).1, hpos⟩
    simp [hempty] at hmem

theorem zero_coeff_same_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0)
    (hzero : ∀ j ∈ incrementCandidates A J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0) :
    incrementPivot A J = cpqrPivot A J := by
  have hfilter := zero_coeff_filters_eq A J hzero
  simp only [incrementPivot, cpqrPivot, if_neg hG, hfilter]

end StructuredColumnSelection
