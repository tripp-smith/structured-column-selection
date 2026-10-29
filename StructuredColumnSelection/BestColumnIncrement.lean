import StructuredColumnSelection.ResidualEnergy
import StructuredColumnSelection.SigmaMinBounds

/-!
# Best unused inverse-trace increment

The inverse-trace increment of a column is `(1 + ‖G⁻¹ Bᵀ a_j‖²) / residual`.
This file bounds the best unused choice of that ratio. It does not say that
the maximum-residual CPQR pivot attains the bound.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

/-- Sum of the quadratic forms `a_jᵀ S a_j` is the trace when the columns of
`A` form an orthogonal-row frame. -/
lemma columns_quadratic_form {k n : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (A : Matrix (Fin k) (Fin n) ℝ)
    (hA : A * Aᵀ = 1) :
    ∑ j : Fin n, (fun i => A i j) ⬝ᵥ (S *ᵥ fun i => A i j) = S.trace := by
  have hmul : ∀ (j : Fin n) (p : Fin k),
      (S *ᵥ fun i => A i j) p = ∑ q : Fin k, S p q * A q j := by
    intro j p
    simp [mulVec, dotProduct]
  have hterm : ∀ j,
      (fun i => A i j) ⬝ᵥ (S *ᵥ fun i => A i j) =
        ∑ p : Fin k, ∑ q : Fin k, A p j * (S p q * A q j) := by
    intro j
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hmul j p, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext p
    rw [Finset.sum_comm]
  have hinner : ∀ p q, ∑ j : Fin n, A p j * (S p q * A q j) =
      S p q * (A * Aᵀ) p q := by
    intro p q
    have hrow : ∑ j : Fin n, A p j * A q j = (A * Aᵀ) p q := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    calc
      ∑ j : Fin n, A p j * (S p q * A q j)
          = ∑ j : Fin n, S p q * (A p j * A q j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = S p q * ∑ j : Fin n, A p j * A q j := by
            rw [← Finset.mul_sum]
      _ = S p q * (A * Aᵀ) p q := by rw [hrow]
  rw [Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hinner p q]
  rw [hA]
  simp [Matrix.trace, Matrix.one_apply]

lemma coeffSq_sum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (_hG : (selectedColGram A J).det ≠ 0) :
    ∑ j : Fin n,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) =
      ((selectedColGram A J)⁻¹).trace := by
  let B := selectedCols A J
  let G := Bᵀ * B
  let M := G⁻¹ * Bᵀ
  change
    ∑ j : Fin n,
      ((G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j)) ⬝ᵥ (G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j))) =
      G⁻¹.trace
  have hM : ∀ j, M *ᵥ (fun i => A i j) = G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j) := by
    intro j
    change ((G⁻¹ * Bᵀ) *ᵥ fun i => A i j) = G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j)
    exact (mulVec_mulVec (fun i => A i j) G⁻¹ Bᵀ).symm
  have hscore : ∀ j,
      ((G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j)) ⬝ᵥ (G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j))) =
        (fun i => A i j) ⬝ᵥ ((Mᵀ * M) *ᵥ fun i => A i j) := by
    intro j
    rw [← hM j]
    have hdot :=
      transpose_mulVec_dot (Mᵀ) (fun i => A i j) (M *ᵥ fun i => A i j)
    rw [Matrix.transpose_transpose] at hdot
    rw [hdot, mulVec_mulVec]
  rw [Finset.sum_congr rfl (fun j _ => hscore j)]
  rw [columns_quadratic_form (Mᵀ * M) A hA]
  rw [Matrix.trace_mul_comm]
  have hsym : Gᵀ = G := by
    change (Bᵀ * B)ᵀ = Bᵀ * B
    simp [Matrix.transpose_mul]
  have hMM : M * Mᵀ = G⁻¹ := by
    change (G⁻¹ * Bᵀ) * (G⁻¹ * Bᵀ)ᵀ = G⁻¹
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, hsym]
    rw [← Matrix.mul_assoc (G⁻¹ * Bᵀ) B G⁻¹, Matrix.mul_assoc G⁻¹ Bᵀ B]
    rw [show Bᵀ * B = G by rfl, Matrix.nonsing_inv_mul G (Ne.isUnit _hG), Matrix.one_mul]
  rw [hMM]

lemma oneHot_dot {t : ℕ} (p : Fin t) :
    (fun q : Fin t => if q = p then (1 : ℝ) else 0) ⬝ᵥ
      (fun q : Fin t => if q = p then (1 : ℝ) else 0) = 1 := by
  simp [dotProduct]

lemma mulVec_oneHot {t : ℕ} (G : Matrix (Fin t) (Fin t) ℝ) (p : Fin t) :
    G *ᵥ (fun q : Fin t => if q = p then (1 : ℝ) else 0) = fun q => G q p := by
  ext q
  simp [mulVec, dotProduct]

lemma selected_coeffSq_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (p : Fin J.card) :
    let j := J.orderEmbOfFin rfl p
    (((selectedColGram A J)⁻¹ *ᵥ
        ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
      ((selectedColGram A J)⁻¹ *ᵥ
        ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = 1 := by
  intro j
  let B := selectedCols A J
  let G := Bᵀ * B
  let e := fun q : Fin J.card => if q = p then (1 : ℝ) else 0
  have hcol : (fun i => A i j) = fun i => B i p := by
    funext i
    simp [j, B, selectedCols]
  have hBt : Bᵀ *ᵥ (fun i => A i j) = fun q => G q p := by
    rw [hcol]
    ext q
    simp [mulVec, dotProduct, G, Matrix.mul_apply, Matrix.transpose_apply]
  have hGe : G *ᵥ e = fun q => G q p := mulVec_oneHot G p
  have hvec : Bᵀ *ᵥ (fun i => A i j) = G *ᵥ e := by
    rw [hBt, ← hGe]
  have happly : G⁻¹ *ᵥ (G *ᵥ e) = e := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul G (Ne.isUnit hG), Matrix.one_mulVec]
  have hcoeff : G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j) = e := by
    rw [hvec, happly]
  change
    (G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j)) ⬝ᵥ (G⁻¹ *ᵥ (Bᵀ *ᵥ fun i => A i j)) = 1
  rw [hcoeff]
  exact oneHot_dot p

lemma selected_coeffSq_sum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ∑ j ∈ J,
      (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) = (J.card : ℝ) := by
  rw [sum_orderEmb J]
  simp_rw [selected_coeffSq_one A J hG]
  simp

lemma exists_ratio_le_sum_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (num den : ι → ℝ) (hne : s.Nonempty)
    (hpos : ∀ i ∈ s, 0 < den i) :
    ∃ i ∈ s, num i / den i ≤ (∑ i ∈ s, num i) / (∑ i ∈ s, den i) := by
  obtain ⟨i, hi, hmin⟩ := exists_min_image s (fun i => num i / den i) hne
  have hden : 0 < ∑ i ∈ s, den i :=
    sum_pos (fun i hi => hpos i hi) hne
  have hcross : ∀ j ∈ s, num i * den j ≤ den i * num j := by
    intro j hj
    have hdiv := hmin j hj
    rw [div_le_div_iff₀ (hpos i hi) (hpos j hj)] at hdiv
    rw [mul_comm (num j) (den i)] at hdiv
    exact hdiv
  have hsum : num i * ∑ j ∈ s, den j ≤ den i * ∑ j ∈ s, num j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum hcross
  refine ⟨i, hi, ?_⟩
  rw [div_le_div_iff₀ (hpos i hi) hden, mul_comm (∑ i ∈ s, num i) (den i)]
  exact hsum

/-- Some unused column has positive residual and inverse-trace increment at
most the average `((n - t) + trace(G⁻¹) - t) / (k - t)`. -/
theorem best_column_increment_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0)
    (ht : J.card < k) :
    ∃ j, j ∉ J ∧ 0 < residualSq A J j ∧
      (1 + (((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
        ((selectedColGram A J)⁻¹ *ᵥ
          ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) / residualSq A J j ≤
        (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
  let score : Fin n → ℝ := fun j =>
    ((selectedColGram A J)⁻¹ *ᵥ ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
      ((selectedColGram A J)⁻¹ *ᵥ ((selectedCols A J)ᵀ *ᵥ fun i => A i j))
  have hscore_nonneg : ∀ j, 0 ≤ score j := by
    intro j
    simp only [score, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hkt : (0 : ℝ) < (k : ℝ) - J.card := by
    have : (J.card : ℝ) < (k : ℝ) := by exact_mod_cast ht
    linarith
  have hsumUnused : ∑ j ∈ unused J, residualSq A J j = (k : ℝ) - J.card :=
    unused_residual_sum A hA J hG
  let pos := (unused J).filter fun j => 0 < residualSq A J j
  have hposne : pos.Nonempty := by
    by_contra hempty
    have hempty' : pos = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ j ∈ unused J, residualSq A J j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      by_cases hlt : 0 < residualSq A J j
      · have : j ∈ pos := mem_filter.mpr ⟨hj, hlt⟩
        simp [hempty'] at this
      · exact le_antisymm (not_lt.mp hlt) (residualSq_nonneg A J j)
    linarith
  have hden : ∑ j ∈ pos, residualSq A J j = (k : ℝ) - J.card := by
    rw [← hsumUnused]
    rw [sum_filter]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hlt : 0 < residualSq A J j
    · simp [hlt]
    · have hnn := residualSq_nonneg A J j
      have h0 : residualSq A J j = 0 := le_antisymm (not_lt.mp hlt) hnn
      simp [h0]
  have hnum_le :
      ∑ j ∈ pos, (1 + score j) ≤ ∑ j ∈ unused J, (1 + score j) := by
    refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j hj hnot => ?_
    have hscore := hscore_nonneg j
    linarith
  have hunused_num :
      ∑ j ∈ unused J, (1 + score j) =
        ((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card := by
    have hsplit : Disjoint J (unused J) := disjoint_sdiff
    have hunion : J ∪ unused J = (univ : Finset (Fin n)) := by
      simp [unused, union_sdiff_of_subset (subset_univ J)]
    have hscore :
        ∑ j : Fin n, score j =
          ∑ j ∈ J, score j + ∑ j ∈ unused J, score j := by
      have := sum_union (f := score) hsplit
      rw [hunion] at this
      exact this
    have hJ : ∑ j ∈ J, score j = (J.card : ℝ) :=
      selected_coeffSq_sum A J hG
    have hall : ∑ j : Fin n, score j = ((selectedColGram A J)⁻¹).trace :=
      coeffSq_sum A hA J hG
    have hunused_score :
        ∑ j ∈ unused J, score j =
          ((selectedColGram A J)⁻¹).trace - (J.card : ℝ) := by
      linarith
    have hcard : (unused J).card = n - J.card := unused_card J
    have hcardle : J.card ≤ n := by
      simpa [Fintype.card_fin] using J.card_le_univ
    have hones : ∑ j ∈ unused J, (1 : ℝ) = (n : ℝ) - J.card := by
      rw [sum_const, nsmul_eq_mul, hcard]
      rw [Nat.cast_sub hcardle]
      ring
    have hadd :
        ∑ j ∈ unused J, (1 + score j) =
          ∑ j ∈ unused J, (1 : ℝ) + ∑ j ∈ unused J, score j := by
      rw [sum_add_distrib]
    linarith
  obtain ⟨j, hj, hratio⟩ :=
    exists_ratio_le_sum_ratio pos (fun j => 1 + score j) (fun j => residualSq A J j)
      hposne (fun j hj => (mem_filter.mp hj).2)
  have hjpos : 0 < residualSq A J j := (mem_filter.mp hj).2
  have hmem : j ∈ unused J := (mem_filter.mp hj).1
  have hjout : j ∉ J := (mem_sdiff.mp hmem).2
  refine ⟨j, hjout, hjpos, ?_⟩
  calc
    (1 + score j) / residualSq A J j
        ≤ (∑ i ∈ pos, (1 + score i)) / ((k : ℝ) - J.card) := by
          simpa [hden] using hratio
    _ ≤ (∑ i ∈ unused J, (1 + score i)) / ((k : ℝ) - J.card) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hkt)
    _ = (((n : ℝ) - J.card) + ((selectedColGram A J)⁻¹).trace - J.card) /
          ((k : ℝ) - J.card) := by
          rw [hunused_num]

end StructuredColumnSelection
