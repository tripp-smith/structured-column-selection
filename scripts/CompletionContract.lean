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
Outcome 2 is the adverse family below. These consumers do not assert a
polynomial inverse bound for every orthogonal-row matrix, a static class,
or the CSSP comparison. `frame38` stays in `SmallInstanceChecks.lean`.
-/

example {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      ∃ x : Fin (widePrefix (wideWidth m) (wideDim m)).card → ℝ,
        A * Aᵀ = 1 ∧
        (∀ i j : Fin (wideDim m),
          A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        (∑ i, (selectedCols A (widePrefix (wideWidth m) (wideDim m)) *ᵥ x) i ^ 2) = 1 ∧
        ((2 * (m : ℝ) / 3) * ((4 : ℝ) / 3) ^ (m - 1)) ^ 2 ≤ ∑ i, x i ^ 2 :=
  milestoneE_wide_adverse_family hm

example (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        A * Aᵀ = 1 ∧
        C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
          (∑ i, (selectedCols A (cpqrSet A) *ᵥ x) i ^ 2) < ∑ i, x i ^ 2 :=
  milestoneE_cpqr_no_joint_polynomial d hC

example :
    ∃ k n : ℕ, ∃ A : Matrix (Fin k) (Fin n) ℝ,
      ∃ x : Fin (cpqrSet A).card → ℝ,
        A * Aᵀ = 1 ∧
        (max ((n : ℝ) ^ 3) (max ((k : ℝ) ^ 3)
          (((k : ℝ) * ((n - k + 1 : ℕ) : ℝ)) ^ 2))) ^ 2 *
          (∑ i, (selectedCols A (cpqrSet A) *ᵥ x) i ^ 2) < ∑ i, x i ^ 2 :=
  milestoneE_cpqr_named_polynomial_obstruction

example {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    spectralNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        spectralNorm E :=
  milestoneF_cssp_spectral A E U S Q hQ J hJ hInv hA

example {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    frobeniusNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        frobeniusNorm E :=
  milestoneF_cssp_frobenius A E U S Q hQ J hJ hInv hA

example {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ)
    (hG : (Bᵀ * B).det ≠ 0)
    (hs : v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v))) ≠ 0) :
    (((appendColumn B v)ᵀ * appendColumn B v)⁻¹).trace =
      ((Bᵀ * B)⁻¹).trace +
        (1 + (((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) /
          (v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) :=
  milestoneE_append_inv_trace_increment B v hG hs

example {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k) :
    ∃ j, j ∉ J ∧ 0 < residualSq A J j ∧
      (1 + (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) / residualSq A J j ≤
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) :=
  milestoneE_best_column_increment_le A hA J hG ht

example {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1)) :
    ∃ j, j ∉ J ∧
      (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) :=
  milestoneE_inv_trace_growth_step A hA J hG ht hf

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ((selectedColGram A J)⁻¹).trace ≤ (k : ℝ) * ((n : ℝ) - k + 1) :=
  milestoneE_minimizing_inv_trace_le A hA

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ J : Finset (Fin n), J.card = k ∧ (selectedColGram A J).det ≠ 0 ∧
      ∀ x : Fin J.card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A J *ᵥ x) :=
  milestoneE_minimizing_inv_spectral_le A hA

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (incrementSet A).card = k ∧
      (selectedColGram A (incrementSet A)).det ≠ 0 ∧
      ((selectedColGram A (incrementSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) ∧
      ∀ x : Fin (incrementSet A).card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A (incrementSet A) *ᵥ x) :=
  milestoneE_increment_set_bound A hA

example :
    ∃ A : Matrix (Fin 2) (Fin 5) ℝ,
      OrthogonalRows A ∧ incrementSet A ≠ cpqrSet A :=
  milestoneE_increment_set_ne_cpqr

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0)
    (hzero : ∀ j ∈ incrementCandidates A J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 0) :
    incrementPivot A J = cpqrPivot A J :=
  milestoneE_zero_coeff_same_pivot A J hG hzero

example {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ m : ℕ, 2 ≤ m ∧
      ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
        A * Aᵀ = 1 ∧
        cpqrSet A = widePrefix (wideWidth m) (wideDim m) ∧
        ∃ jMin jMax : Fin (wideWidth m),
          τ * (∑ i, A i jMin ^ 2) < ∑ i, A i jMax ^ 2 ∧
          (8 * ((m * m : ℕ) : ℝ)) * (∑ i, A i jMin ^ 2) < ∑ i, A i jMax ^ 2 := by
  obtain ⟨m, hm, A, horth, hcpqr, jMin, jMax, hτe, h8⟩ :=
    milestoneE_wide_leverage_escape hτ
  refine ⟨m, hm, A, ?_, ?_, jMin, jMax, ?_, ?_⟩
  · simpa [OrthogonalRows] using horth
  · simpa [wideDim] using hcpqr
  · simpa [residualSq_empty] using hτe
  · have hcoeff :
        (8 * ((m * m : ℕ) : ℝ)) * residualSq A ∅ jMin < residualSq A ∅ jMax := h8
    simpa [residualSq_empty] using hcoeff

/-!
The consumers below keep extra hypotheses. They are not outcome 1.
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
