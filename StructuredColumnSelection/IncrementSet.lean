import StructuredColumnSelection.InvSpectralBound

/-!
# Deterministic increment pivot

`cpqrPivot` chooses the largest residual. The increment pivot chooses
the least index among unused columns that minimize the inverse-trace
increment `(1 + ‖G⁻¹ Bᵀ a_j‖²) / residual`. On orthogonal rows that
set has cardinality `k`, invertible Gram, inverse trace at most
`k (n - k + 1)`, and squared inverse operator norm at most
`1 + k (n - k)`.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

noncomputable def incrementCandidates {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) : Finset (Fin n) :=
  (unused J).filter fun j => 0 < residualSq A J j

noncomputable def incrementRatio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n) : ℝ :=
  (1 + (((selectedColGram A J)⁻¹ *ᵥ
      ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
    ((selectedColGram A J)⁻¹ *ᵥ
      ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) / residualSq A J j

noncomputable def incrementBest {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) : ℝ :=
  let s := incrementCandidates A J
  if h : s.Nonempty then
    (s.image (incrementRatio A J)).min' (h.image (incrementRatio A J))
  else
    0

noncomputable def incrementPivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) : Option (Fin n) :=
  if (selectedColGram A J).det = 0 then
    none
  else
    let t := (incrementCandidates A J).filter fun j =>
      incrementRatio A J j = incrementBest A J
    if h : t.Nonempty then some (t.min' h) else none

noncomputable def incrementIterate {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 =>
    match incrementPivot A (incrementIterate A t) with
    | some j => insert j (incrementIterate A t)
    | none => incrementIterate A t

noncomputable def incrementSet {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) : Finset (Fin n) :=
  incrementIterate A k

lemma incrementBest_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    {j : Fin n} (hj : j ∈ incrementCandidates A J) :
    incrementBest A J ≤ incrementRatio A J j := by
  have hs : (incrementCandidates A J).Nonempty := ⟨j, hj⟩
  have hmem : incrementRatio A J j ∈
      (incrementCandidates A J).image (incrementRatio A J) :=
    mem_image_of_mem _ hj
  unfold incrementBest
  rw [dif_pos hs]
  exact min'_le ((incrementCandidates A J).image (incrementRatio A J)) _ hmem

lemma increment_insert_of_ratio {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1))
    {j : Fin n} (hj : j ∉ J) (hpos : 0 < residualSq A J j)
    (hratio : incrementRatio A J j ≤
      (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
        ((k : ℝ) - J.card)) :
    (selectedColGram A (insert j J)).det ≠ 0 ∧
      ((selectedColGram A (insert j J))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) := by
  have hschur := residualSq_eq_schur A J j hG
  have hs : (fun i => A i j) ⬝ᵥ (fun i => A i j) -
      (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) ≠ 0 := by
    rw [← hschur]
    exact ne_of_gt hpos
  have hG' : ((selectedCols A J)ᵀ * selectedCols A J).det ≠ 0 := by
    simpa [selectedColGram] using hG
  have hupdate :=
    append_inv_trace_increment (selectedCols A J) (fun i => A i j) hG' hs
  have havg :
      ((selectedColGram A J)⁻¹).trace +
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) :=
    trace_bound_step ht hf
  have happ_le :
      (((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) := by
    simp only [selectedColGram] at havg
    rw [hupdate]
    have hratio' :
        (1 + (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) /
          ((fun i => A i j) ⬝ᵥ (fun i => A i j) -
            (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
              (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
                ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) ≤
        (((n : ℝ) - J.card) +
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
      simpa [incrementRatio, selectedColGram, hschur] using hratio
    exact le_trans
      (add_le_add_right hratio'
        (((selectedCols A J)ᵀ * selectedCols A J)⁻¹).trace) havg
  have hmul := residualSq_mul_gram A hj (Or.inr hG)
  have hinsert_det : (selectedColGram A (insert j J)).det ≠ 0 := by
    by_cases h0 : J.card = 0
    · have hmul' :
          residualSq A J j = (selectedColGram A (insert j J)).det := by
        simpa [h0] using hmul
      rw [← hmul']
      exact ne_of_gt hpos
    · have hmul' :
          residualSq A J j * (selectedColGram A J).det =
            (selectedColGram A (insert j J)).det := by
        simpa [h0] using hmul
      rw [← hmul']
      exact mul_ne_zero (ne_of_gt hpos) hG
  have happdet :
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
    rw [appendColumn_gram_det_eq_insert A hj]
    exact hinsert_det
  have heq := append_inv_trace_eq_insert A hj happdet
  refine ⟨hinsert_det, ?_⟩
  rw [← heq]
  exact happ_le

lemma incrementPivot_spec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k)
    (hf : ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) * ((n : ℝ) - J.card + 1) / ((k : ℝ) - J.card + 1)) :
    ∃ j, incrementPivot A J = some j ∧ j ∉ J ∧
      (selectedColGram A (insert j J)).det ≠ 0 ∧
      ((selectedColGram A (insert j J))⁻¹).trace ≤
        ((J.card : ℝ) + 1) * ((n : ℝ) - J.card) / ((k : ℝ) - J.card) := by
  obtain ⟨j0, hj0, hpos0, hratio0⟩ := best_column_increment_le A hA J hG ht
  have hj0c : j0 ∈ incrementCandidates A J := by
    refine mem_filter.mpr ⟨?_, hpos0⟩
    simp [unused, hj0]
  have hbest_le : incrementBest A J ≤
      (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
        ((k : ℝ) - J.card) :=
    (incrementBest_le A J hj0c).trans (by simpa [incrementRatio] using hratio0)
  have hs : (incrementCandidates A J).Nonempty := ⟨j0, hj0c⟩
  have hbest_mem :=
    min'_mem ((incrementCandidates A J).image (incrementRatio A J))
      (hs.image (incrementRatio A J))
  obtain ⟨jMin, hjMin, hjMinEq⟩ := mem_image.mp hbest_mem
  have hbest_eq : incrementRatio A J jMin = incrementBest A J := by
    unfold incrementBest
    rw [dif_pos hs]
    exact hjMinEq
  let t := (incrementCandidates A J).filter fun j =>
    incrementRatio A J j = incrementBest A J
  have htne : t.Nonempty := ⟨jMin, mem_filter.mpr ⟨hjMin, hbest_eq⟩⟩
  have hpivot : incrementPivot A J = some (t.min' htne) := by
    unfold incrementPivot
    rw [if_neg hG]
    simp [t, htne]
  refine ⟨t.min' htne, hpivot, ?_, ?_, ?_⟩
  · have hmem := min'_mem t htne
    have hcand := (mem_filter.mp hmem).1
    have hunused := (mem_filter.mp hcand).1
    simpa [unused] using hunused
  · have hmem := min'_mem t htne
    have hcand := (mem_filter.mp hmem).1
    have hpos := (mem_filter.mp hcand).2
    have hratio_eq := (mem_filter.mp hmem).2
    have hnot : t.min' htne ∉ J := by
      have hunused := (mem_filter.mp hcand).1
      simpa [unused] using hunused
    have hratio : incrementRatio A J (t.min' htne) ≤
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
      rw [hratio_eq]
      exact hbest_le
    exact (increment_insert_of_ratio A J hG ht hf hnot hpos hratio).1
  · have hmem := min'_mem t htne
    have hcand := (mem_filter.mp hmem).1
    have hpos := (mem_filter.mp hcand).2
    have hratio_eq := (mem_filter.mp hmem).2
    have hnot : t.min' htne ∉ J := by
      have hunused := (mem_filter.mp hcand).1
      simpa [unused] using hunused
    have hratio : incrementRatio A J (t.min' htne) ≤
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
      rw [hratio_eq]
      exact hbest_le
    exact (increment_insert_of_ratio A J hG ht hf hnot hpos hratio).2

lemma incrementIterate_spec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∀ t, t ≤ k →
      (incrementIterate A t).card = t ∧
        (selectedColGram A (incrementIterate A t)).det ≠ 0 ∧
        ((selectedColGram A (incrementIterate A t))⁻¹).trace ≤
          (t : ℝ) * ((n : ℝ) - t + 1) / ((k : ℝ) - t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp [incrementIterate]
    · rw [incrementIterate, selectedColGram_empty_det]
      norm_num
    · rw [incrementIterate, selectedColGram_empty_inv_trace]
      simp
  | succ t ih =>
    intro ht
    obtain ⟨hcard, hG, hf⟩ := ih (Nat.le_of_succ_le ht)
    have hlt : (incrementIterate A t).card < k := by
      rw [hcard]
      exact Nat.lt_of_succ_le ht
    have hfJ : ((selectedColGram A (incrementIterate A t))⁻¹).trace ≤
        ((incrementIterate A t).card : ℝ) *
          ((n : ℝ) - (incrementIterate A t).card + 1) /
            ((k : ℝ) - (incrementIterate A t).card + 1) := by
      simpa [hcard] using hf
    obtain ⟨j, hpivot, hj, hdet, htr⟩ :=
      incrementPivot_spec A hA (incrementIterate A t) hG hlt hfJ
    have hstep : incrementIterate A (t + 1) =
        insert j (incrementIterate A t) := by
      simp [incrementIterate, hpivot]
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep, card_insert_of_notMem hj, hcard]
    · have hdet_eq :
          (selectedColGram A (incrementIterate A (t + 1))).det =
            (selectedColGram A (insert j (incrementIterate A t))).det :=
        congrArg (fun S => (selectedColGram A S).det) hstep
      rw [hdet_eq]
      exact hdet
    · have htr_eq :
          ((selectedColGram A (incrementIterate A (t + 1)))⁻¹).trace =
            ((selectedColGram A (insert j (incrementIterate A t)))⁻¹).trace :=
        congrArg (fun S => ((selectedColGram A S)⁻¹).trace) hstep
      rw [htr_eq]
      rw [hcard] at htr
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := Nat.cast_succ t
      have hnum : (n : ℝ) - ((t : ℝ) + 1) + 1 = (n : ℝ) - t := by ring
      have hden : (k : ℝ) - ((t : ℝ) + 1) + 1 = (k : ℝ) - t := by ring
      rw [hcast, hnum, hden]
      exact htr

/-- The least-index increment pivot selects `k` columns whose inverse
trace is at most `k (n - k + 1)` and which satisfy
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

This is not the max-residual CPQR pivot and does not close outcome 3. -/
theorem increment_set_bound {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (incrementSet A).card = k ∧
      (selectedColGram A (incrementSet A)).det ≠ 0 ∧
      ((selectedColGram A (incrementSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) ∧
      ∀ x : Fin (incrementSet A).card → ℝ,
        vecEnergy x ≤
          (1 + (k : ℝ) * ((n : ℝ) - k)) *
            vecEnergy (selectedCols A (incrementSet A) *ᵥ x) := by
  obtain ⟨hcard, hG, hf⟩ := incrementIterate_spec A hA k le_rfl
  have hden : (k : ℝ) - k + 1 = 1 := by ring
  have htrace : ((selectedColGram A (incrementSet A))⁻¹).trace ≤
      (k : ℝ) * ((n : ℝ) - k + 1) := by
    rw [hden, div_one] at hf
    exact hf
  refine ⟨hcard, hG, htrace, ?_⟩
  intro x
  have henergy :=
    selectedCols_energy_le_shifted_trace A hA (incrementSet A) hG x
  have hshift : ((selectedColGram A (incrementSet A))⁻¹).trace -
      ((incrementSet A).card : ℝ) + 1 ≤
      1 + (k : ℝ) * ((n : ℝ) - k) := by
    have hcast : ((incrementSet A).card : ℝ) = (k : ℝ) := by
      exact_mod_cast hcard
    rw [hcast]
    have htrace' : ((selectedColGram A (incrementSet A))⁻¹).trace ≤
        (k : ℝ) * ((n : ℝ) - k + 1) := htrace
    linarith
  have hBx : 0 ≤ vecEnergy (selectedCols A (incrementSet A) *ᵥ x) :=
    vecEnergy_nonneg _
  have hscaled : vecEnergy (selectedCols A (incrementSet A) *ᵥ x) *
      (((selectedColGram A (incrementSet A))⁻¹).trace -
        ((incrementSet A).card : ℝ) + 1) ≤
      vecEnergy (selectedCols A (incrementSet A) *ᵥ x) *
        (1 + (k : ℝ) * ((n : ℝ) - k)) :=
    mul_le_mul_of_nonneg_left hshift hBx
  exact henergy.trans (hscaled.trans (le_of_eq (mul_comm _ _)))

end StructuredColumnSelection
