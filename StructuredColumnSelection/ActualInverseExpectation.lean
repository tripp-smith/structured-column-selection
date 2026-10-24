import StructuredColumnSelection.SigmaMinBounds

/-! Actual volume-weighted inverse traces, including singular-support frames.
The adjugate sum is an upper bound on the true expectation; equality requires
additional full support. Singular blocks have zero volume probability. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

/-- Actual inverse Gram trace. Mathlib totalizes the inverse on singular
matrices; every such block has zero weight in the distribution below. On a
square nonsingular block this is the inverse Frobenius norm squared. -/
noncomputable def selectedInvTrace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) : ℝ :=
  ((selectedColGram A J)⁻¹).trace

lemma volumeWeight_eq_zero_of_singular {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)}
    (hJ : J.card = k) (hz : (selectedColGram A J).det = 0) :
    volumeWeight A J = 0 := by
  rw [volumeWeight_eq_selectedColGram_det A hJ, hz]

lemma actual_inv_weight_le_proxy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} (hJ : J.card = k) :
    volumeWeight A J * selectedInvTrace A J ≤ invFrobWeight A J := by
  by_cases hG : (selectedColGram A J).det = 0
  · rw [volumeWeight_eq_zero_of_singular A hJ hG, zero_mul]
    exact invFrobWeight_nonneg A J
  · exact (invFrobWeight_eq_volumeWeight_mul_inv_trace A hJ hG).symm.le

theorem actual_expected_inv_trace_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * selectedInvTrace A J ≤
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) := by
  calc _ ≤ ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, invFrobWeight A J :=
      sum_le_sum fun J hJ => actual_inv_weight_le_proxy A (mem_powersetCard.mp hJ).2
    _ = _ := expectedInvFrobSq A hA

theorem actual_expected_inv_trace_eq_of_full_support {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hfull : ∀ J : Finset (Fin n), J.card = k → (selectedColGram A J).det ≠ 0) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * selectedInvTrace A J =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) := by
  rw [← expectedInvFrobSq A hA]
  apply sum_congr rfl
  intro J hJ
  have hc := (mem_powersetCard.mp hJ).2
  exact (invFrobWeight_eq_volumeWeight_mul_inv_trace A hc (hfull J hc)).symm

theorem singular_volume_mass_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (fun J => (selectedColGram A J).det = 0), volumeWeight A J = 0 := by
  apply sum_eq_zero
  intro J hJ
  exact volumeWeight_eq_zero_of_singular A
    (mem_powersetCard.mp (mem_filter.mp hJ).1).2 (mem_filter.mp hJ).2

/-- Literal nonsingularity plus actual inverse-trace threshold event. -/
def actualInvTraceGood {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (t : ℝ) (J : Finset (Fin n)) : Prop :=
  (selectedColGram A J).det ≠ 0 ∧ selectedInvTrace A J ≤ t

lemma actual_bad_mass_eq_proxy_bad_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (t : ℝ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (fun J => ¬ actualInvTraceGood A t J), volumeWeight A J =
      ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (invFrobExceeds A t), volumeWeight A J := by
  classical
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro J hJ
  have hc := (mem_powersetCard.mp hJ).2
  by_cases hG : (selectedColGram A J).det = 0
  · simp [volumeWeight_eq_zero_of_singular A hc hG]
  · have hw : 0 < volumeWeight A J :=
      lt_of_le_of_ne (volumeWeight_nonneg A J)
        (by rw [volumeWeight_eq_selectedColGram_det A hc]; exact Ne.symm hG)
    have hevent : (¬ actualInvTraceGood A t J) ↔ invFrobExceeds A t J := by
      simp only [actualInvTraceGood, hG, ne_eq, not_false_eq_true, true_and,
        not_le, invFrobExceeds, invFrobWeight_eq_volumeWeight_mul_inv_trace A hc hG,
        selectedInvTrace, mul_lt_mul_iff_right₀ hw]
    simp only [hevent]

theorem actual_inv_trace_good_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInvTraceGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J := by
  classical
  have hpart := sum_filter_add_sum_filter_not
    ((univ : Finset (Fin n)).powersetCard k)
    (actualInvTraceGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ))
    (volumeWeight A)
  rw [volumeWeights_sum_eq_one A hA, actual_bad_mass_eq_proxy_bad_mass] at hpart
  have htail := markovInvFrob A hA hδ
  linarith

/-- An explicit inverse-energy bound on the selected column map. -/
def actualInverseEnergyGood {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (t : ℝ) (J : Finset (Fin n)) : Prop :=
  (selectedColGram A J).det ≠ 0 ∧ ∀ x : Fin J.card → ℝ,
    vecEnergy x ≤ t * vecEnergy (selectedCols A J *ᵥ x)

theorem actual_inverse_energy_good_mass {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInverseEnergyGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J := by
  classical
  refine (actual_inv_trace_good_mass A hA hδ).trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨hmem, hG, htr⟩ := mem_filter.mp hJ
    apply mem_filter.mpr
    refine ⟨hmem, hG, fun x => ?_⟩
    calc vecEnergy x
        ≤ vecEnergy (selectedCols A J *ᵥ x) * selectedInvTrace A J :=
          selectedCols_energy_mul_inv_trace_ge A J hG x
      _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right htr (vecEnergy_nonneg _)
  · intro J _ _
    exact volumeWeight_nonneg A J

end StructuredColumnSelection

namespace StructuredColumnSelection.ActualInverseWitness
open Classical Finset
open scoped Matrix

def zeroColumnFrame : Matrix (Fin 1) (Fin 2) ℝ :=
  fun _ j => if j = 0 then 1 else 0

theorem zeroColumnFrame_orthogonal : OrthogonalRows zeroColumnFrame := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [OrthogonalRows, Matrix.mul_apply, zeroColumnFrame, Fin.sum_univ_two]

private lemma one_row_proxy (J : Finset (Fin 2)) (hJ : J.card = 1) :
    invFrobWeight zeroColumnFrame J = 1 := by
  rw [invFrobWeight, volumeWeightedInvGram_eq zeroColumnFrame hJ]
  simp [Matrix.trace]

private lemma witness_volume (j : Fin 2) :
    volumeWeight zeroColumnFrame {j} = (if j = 0 then 1 else 0) := by
  rw [volumeWeight_eq zeroColumnFrame (by simp)]
  have hcol : ∀ p : Fin 1, ({j} : Finset (Fin 2)).orderEmbOfFin (by simp) p = j := by
    intro p
    exact mem_singleton.mp (orderEmbOfFin_mem _ _ p)
  simp [colsSubmatrix, hcol, zeroColumnFrame]

/-- Exact real-arithmetic obstruction to the unconditional equality in SPEC §5. -/
theorem zeroColumnFrame_actual_expectation :
    ∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1,
      volumeWeight zeroColumnFrame J * selectedInvTrace zeroColumnFrame J = 1 := by
  have hsets : (univ : Finset (Fin 2)).powersetCard 1 = {{0}, {1}} := by decide
  have hvol0 : volumeWeight zeroColumnFrame {0} = 1 := by simp [witness_volume]
  have hvol1 : volumeWeight zeroColumnFrame {1} = 0 := by simp [witness_volume]
  have hG : (selectedColGram zeroColumnFrame {0}).det ≠ 0 := by
    rw [← volumeWeight_eq_selectedColGram_det zeroColumnFrame (by simp), hvol0]
    norm_num
  have hterm := invFrobWeight_eq_volumeWeight_mul_inv_trace zeroColumnFrame
    (J := {0}) (by simp) hG
  rw [one_row_proxy _ (by simp)] at hterm
  simpa [hsets, hvol1, selectedInvTrace] using hterm.symm

end StructuredColumnSelection.ActualInverseWitness
