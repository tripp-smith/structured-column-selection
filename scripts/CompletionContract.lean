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

-- Bounded core only: these consumers do not assert an adverse-family endpoint.
example {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : (∑ i : Fin k, ∑ j : Fin k, R i j ^ 2) ≤ 1) (t : ℕ) (ht : 0 < t) :
    ∃ A : Matrix (Fin k) (Fin (k+k*t)) ℝ, A * Aᵀ = 1 ∧
      (∀ i j : Fin k, A i (j.castAdd (k*t)) = R i j) ∧
      ∀ j : Fin (k*t), (∑ i : Fin k, A i (j.natAdd k)^2) ≤ (k : ℝ) / t :=
  milestoneE_wide_completion_orthogonal R hR t ht

example {k n : ℕ} (hkn : k ≤ n) (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0) :
    ∀ t ≤ k, (selectedColGram A (widePrefix n t)).det ≠ 0 ∧
      ∀ x, selectedProjector A (widePrefix n t) *ᵥ x =
        (fun i : Fin k => if (i : ℕ) < t then x i else 0) :=
  milestoneE_triangular_prefix_projector hkn A hupper hdiag

example {k n : ℕ} (hkn : k ≤ n) (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (t : ℕ) (ht : t ≤ k) (j : Fin n) :
    residualSq A (widePrefix n t) j =
      ∑ i : Fin k, if t ≤ (i : ℕ) then A i j ^ 2 else 0 :=
  milestoneE_triangular_prefix_residual hkn A hupper hdiag t ht j

example {k n : ℕ} (hkn : k ≤ n) (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (htail : ∀ p : Fin k, ∀ j : Fin n, (p : ℕ) < (j : ℕ) →
      (∑ i : Fin k, if (p : ℕ) ≤ (i : ℕ) then A i j ^ 2 else 0) <
        A p (Fin.castLE hkn p)^2) :
    ∀ t ≤ k, cpqrIterate A t = widePrefix n t :=
  milestoneE_triangular_prefix_pivots hkn A hupper hdiag htail

example {m : ℕ} (hm : 2 ≤ m) {i : ℕ} (hi : i < m*m) :
    (1 / (2 * ((m*m : ℕ) : ℝ))) / 2 <
      (1 / (2 * ((m*m : ℕ) : ℝ))) *
        ((4*(m : ℝ)^2-1)/(4*(m : ℝ)^2+1))^i :=
  milestoneE_wide_parameter_diagonal_lower hm hi

/-!
SPEC §16 Milestone E consumers below keep the extra hypotheses in the type.
They do not assert a joint polynomial inverse bound for every orthogonal-row
matrix. Outcome 2 has no consumer here: the 3×8 witness stays in
`SmallInstanceChecks.lean` and is not re-exported. Outcome 3 needs that
witness to pass the named polynomial, which it does not. Milestone F is
not asserted.
-/

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((n : ℝ) - k + 1) * ((4 : ℝ)^k + 6*k - 1) / 9 :=
  milestoneE_pivot_gram_inv_trace_le A hA

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hbi : gsUBidiagonal A hA) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) :=
  milestoneE_bidiagonal_U_inv_trace_le A hA hbi

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hb : gsUColumnBudget A hA) :
    ((pivotGram A hA)⁻¹).trace ≤
      ((k : ℝ) * (k + 1) / 2) * ((n : ℝ) - k + 1) :=
  milestoneE_column_budget_inv_trace_le A hA hb

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n.choose k : ℝ) *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
  milestoneE_cpqr_inv_energy_le_choose A hA x

example {k n d : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hd : MinDimLe k n d) (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n : ℝ) ^ d *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
  milestoneE_cpqr_inv_energy_le_of_minDim A hA hd x
