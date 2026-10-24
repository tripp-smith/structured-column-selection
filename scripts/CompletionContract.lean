import StructuredColumnSelection.Theorems

/-! Public-only expected-type consumers. Extra support/coefficient assumptions
cannot be added silently to the all-frame inequality/probability contracts.
The original unconditional equality is intentionally not asserted: it is false. -/
open StructuredColumnSelection Classical Finset
open scoped Matrix

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * ((selectedColGram A J)⁻¹).trace ≤
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  milestoneD_actual_expected_inv_trace_le A hA

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (fun J => (selectedColGram A J).det ≠ 0 ∧
        ∀ x : Fin J.card → ℝ, vecEnergy x ≤
          (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ) *
            vecEnergy (selectedCols A J *ᵥ x)), volumeWeight A J :=
  by
    classical
    have hset :
        ((univ : Finset (Fin n)).powersetCard k).filter
          (actualInverseEnergyGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)) =
        ((univ : Finset (Fin n)).powersetCard k).filter
          (fun J => (selectedColGram A J).det ≠ 0 ∧
            ∀ x : Fin J.card → ℝ, vecEnergy x ≤
              (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ) *
                vecEnergy (selectedCols A J *ᵥ x)) := by
      ext J
      simp only [mem_filter, actualInverseEnergyGood]
    simpa only [hset] using (milestoneD_actual_inverse_energy_good_mass A hA hδ)

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (fun J => (selectedColGram A J).det = 0), volumeWeight A J = 0 :=
  milestoneD_singular_volume_mass_zero A

example : ∃ A : Matrix (Fin 1) (Fin 2) ℝ, OrthogonalRows A ∧
    (∑ J ∈ (univ : Finset (Fin 2)).powersetCard 1,
      volumeWeight A J * ((selectedColGram A J)⁻¹).trace) ≠ (2 : ℝ) :=
  milestoneD_actual_expectation_equality_obstruction

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hfull : ∀ J : Finset (Fin n), J.card = k → (selectedColGram A J).det ≠ 0) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeight A J * ((selectedColGram A J)⁻¹).trace =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  milestoneD_actual_expected_inv_trace_eq_of_full_support A hA hfull


-- All-frame reverse recursion law; no full-support, coefficient or endpoint-card assumption.
example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) :
    reverseEndpointMass A (n-k) univ J = volumeWeight A J :=
  milestoneD_reverse_sampler_law A hA J

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (S : Finset (Fin n))
    (hs : k < S.card) (hV : 0 < retainedVolume A S) :
    (∀ i ∈ S, 0 ≤ reverseDeleteProb A S i) ∧
      ∑ i ∈ S, reverseDeleteProb A S i = 1 :=
  milestoneB_reverse_transition_normalization A S hs hV

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
      (actualInverseEnergyGood A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      reverseEndpointMass A (n-k) univ J :=
  milestoneD_reverse_inverse_energy_good_mass A hA hδ
