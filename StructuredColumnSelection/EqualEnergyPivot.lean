import StructuredColumnSelection.OrthogonalColumns
import StructuredColumnSelection.ZeroCoeffPivot

/-!
# Equal column energy, second CPQR pivot

If every column has the same energy, that energy is `k / n`. On a
one-column Gram the inverse-trace ratio is strictly decreasing in the
residual, so max-residual CPQR and the increment pivot select the same
second column. The two-column inverse trace is at most
`2 (n - 1) / (k - 1)`.

Equal energy is leverage ratio `1`. The estimate
`‖G⁻¹ v‖² ≤ trace(G⁻¹) · q` does not close later steps, so this does
not bound a `k`-set for `k > 2` and does not close outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma equal_column_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hn : 0 < n) (j : Fin n) :
    colInner A j j = (k : ℝ) / n := by
  have hsum := energy_sum A hA
  have hconst : ∑ i : Fin n, colInner A i i = ∑ i : Fin n, colInner A j j := by
    refine Finset.sum_congr rfl fun i _ => hE i j
  rw [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [eq_div_iff hn0, mul_comm]
  exact hsum

lemma colInner_eq_residualSq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    colInner A j j = residualSq A ∅ j := by
  rw [residualSq_empty, colInner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two]

lemma residual_ratio_antitone {e r₁ r₂ : ℝ}
    (he : 0 < e) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hle : r₁ ≤ r₂) :
    (2 * e - r₂) / (e * r₂) ≤ (2 * e - r₁) / (e * r₁) := by
  rw [div_le_div_iff₀ (mul_pos he hr₂) (mul_pos he hr₁)]
  have hring : (2 * e - r₁) * (e * r₂) - (2 * e - r₂) * (e * r₁) =
      2 * e * e * (r₂ - r₁) := by ring
  have hnonneg : 0 ≤ 2 * e * e * (r₂ - r₁) := by
    have hr : 0 ≤ r₂ - r₁ := sub_nonneg.mpr hle
    have he2 : 0 ≤ e * e := mul_self_nonneg e
    positivity
  linarith

lemma residual_ratio_strict_anti {e r₁ r₂ : ℝ}
    (he : 0 < e) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : r₁ < r₂) :
    (2 * e - r₂) / (e * r₂) < (2 * e - r₁) / (e * r₁) := by
  rw [div_lt_div_iff₀ (mul_pos he hr₂) (mul_pos he hr₁)]
  have hring : (2 * e - r₁) * (e * r₂) - (2 * e - r₂) * (e * r₁) =
      2 * e * e * (r₂ - r₁) := by ring
  have hpos : 0 < 2 * e * e * (r₂ - r₁) := by
    have hr : 0 < r₂ - r₁ := sub_pos.mpr hlt
    have he2 : 0 < e * e := mul_pos he he
    positivity
  linarith

def singletonIdx {n : ℕ} (p : Fin n) : Fin ({p} : Finset (Fin n)).card :=
  ⟨0, by rw [Finset.card_singleton]; exact Nat.zero_lt_one⟩

lemma singletonIdx_unique {n : ℕ} (p : Fin n)
    (q : Fin ({p} : Finset (Fin n)).card) :
    q = singletonIdx p := by
  have hsub : Subsingleton (Fin ({p} : Finset (Fin n)).card) := by
    rw [Finset.card_singleton]
    infer_instance
  exact @Subsingleton.elim _ hsub q (singletonIdx p)

lemma sum_singletonIdx {n : ℕ} (p : Fin n)
    (f : Fin ({p} : Finset (Fin n)).card → ℝ) :
    ∑ q, f q = f (singletonIdx p) := by
  refine Finset.sum_eq_single (singletonIdx p) ?_ ?_
  · intro q _ hq
    exact absurd (singletonIdx_unique p q) hq
  · intro hq
    exact False.elim (hq (Finset.mem_univ _))

lemma singleton_gram_apply {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p : Fin n)
    (a b : Fin ({p} : Finset (Fin n)).card) :
    selectedColGram A {p} a b = colInner A p p := by
  rw [selectedColGram, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.transpose_apply, selectedCols, Matrix.submatrix_apply,
    orderEmbOfFin_singleton_apply]

lemma singleton_gram_inv {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p : Fin n)
    (he : colInner A p p ≠ 0) :
    (selectedColGram A {p})⁻¹ = fun _ _ => (colInner A p p)⁻¹ := by
  let B : Matrix (Fin ({p} : Finset (Fin n)).card) (Fin ({p} : Finset (Fin n)).card) ℝ :=
    fun _ _ => (colInner A p p)⁻¹
  have hmul : selectedColGram A {p} * B = 1 := by
    ext a b
    rw [Matrix.mul_apply, sum_singletonIdx p, singleton_gram_apply A p a (singletonIdx p),
      Matrix.one_apply]
    have hab : a = b :=
      (singletonIdx_unique p a).trans (singletonIdx_unique p b).symm
    simp only [B]
    rw [hab, if_pos rfl]
    exact mul_inv_cancel₀ he
  simpa [B] using Matrix.inv_eq_right_inv hmul

lemma singleton_bt_apply {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p j : Fin n)
    (q : Fin ({p} : Finset (Fin n)).card) :
    ((selectedCols A {p})ᵀ *ᵥ fun i => A i j) q = colInner A p j := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, selectedCols, Matrix.submatrix_apply,
    orderEmbOfFin_singleton_apply]
  rfl

lemma singleton_coeff_apply {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p j : Fin n)
    (he : colInner A p p ≠ 0)
    (q : Fin ({p} : Finset (Fin n)).card) :
    ((selectedColGram A {p})⁻¹ *ᵥ
        ((selectedCols A {p})ᵀ *ᵥ fun i => A i j)) q =
      colInner A p j / colInner A p p := by
  rw [Matrix.mulVec_apply_eq_sum, singleton_gram_inv A p he, sum_singletonIdx p,
    singleton_bt_apply]
  rw [div_eq_mul_inv, mul_comm]

lemma singleton_coeff_sq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p j : Fin n)
    (he : colInner A p p ≠ 0) :
    (((selectedColGram A {p})⁻¹ *ᵥ
          ((selectedCols A {p})ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
      ((selectedColGram A {p})⁻¹ *ᵥ
        ((selectedCols A {p})ᵀ *ᵥ fun i => A i j))) =
      colInner A p j ^ 2 / colInner A p p ^ 2 := by
  rw [dotProduct, sum_singletonIdx p, singleton_coeff_apply A p j he]
  rw [div_mul_div_comm, ← pow_two, ← pow_two]

lemma singleton_proj {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (p j : Fin n)
    (he : colInner A p p ≠ 0) :
    (((selectedCols A {p})ᵀ *ᵥ fun i => A i j) ⬝ᵥ
      ((selectedColGram A {p})⁻¹ *ᵥ
        ((selectedCols A {p})ᵀ *ᵥ fun i => A i j))) =
      colInner A p j ^ 2 / colInner A p p := by
  rw [dotProduct, sum_singletonIdx p, singleton_bt_apply, singleton_coeff_apply A p j he]
  rw [← mul_div_assoc, ← pow_two]

lemma singleton_ratio_of_equal_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (p j : Fin n) (he : 0 < colInner A p p) :
    incrementRatio A {p} j =
      (2 * colInner A p p - residualSq A {p} j) /
        (colInner A p p * residualSq A {p} j) := by
  set e : ℝ := colInner A p p
  have hGdet : (selectedColGram A {p}).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero A p (by
      rw [← colInner_eq_residualSq]
      exact he)
  have hv : (fun i => A i j) ⬝ᵥ (fun i => A i j) = colInner A j j := rfl
  have hres : residualSq A {p} j = e - colInner A p j ^ 2 / e := by
    rw [residualSq_eq_schur A {p} j hGdet, hv, hE j p,
      singleton_proj A p j (ne_of_gt he)]
  have hc := singleton_coeff_sq A p j (ne_of_gt he)
  unfold incrementRatio
  rw [hc]
  have hqe : colInner A p j ^ 2 / e = e - residualSq A {p} j := by
    have hsub : residualSq A {p} j + colInner A p j ^ 2 / e = e := by
      rw [hres]
      ring
    linarith
  have hdiv : (colInner A p j ^ 2 / e) / e = colInner A p j ^ 2 / e ^ 2 := by
    rw [div_div, ← pow_two e]
  rw [← hdiv, hqe]
  have hnum : 1 + (e - residualSq A {p} j) / e =
      (2 * e - residualSq A {p} j) / e := by
    rw [← div_self (ne_of_gt he), ← add_div]
    congr 1
    ring
  rw [hnum, div_div]

lemma equal_energy_incrementBest {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (p : Fin n) (he : 0 < colInner A p p)
    (hs : (incrementCandidates A {p}).Nonempty) :
    incrementBest A {p} =
      (2 * colInner A p p - maxResidual A {p}) /
        (colInner A p p * maxResidual A {p}) := by
  have hmax := maxResidual_eq_candidate_sup A {p} hs
  obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup' hs (residualSq A {p})
  have hres : residualSq A {p} j = maxResidual A {p} := by
    rw [← hjsup, hmax]
  have hposj : 0 < residualSq A {p} j := (mem_filter.mp hj).2
  have hmaxpos : 0 < maxResidual A {p} := by
    rw [← hres]
    exact hposj
  unfold incrementBest
  rw [dif_pos hs, min'_eq_iff]
  refine ⟨?_, ?_⟩
  · have hratio := singleton_ratio_of_equal_energy A hE p j he
    rw [hres] at hratio
    rw [← hratio]
    exact mem_image_of_mem (incrementRatio A {p}) hj
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
    have hposi : 0 < residualSq A {p} i := (mem_filter.mp hi).2
    have hle : residualSq A {p} i ≤ maxResidual A {p} := by
      rw [hmax, le_sup'_iff]
      exact ⟨i, hi, le_rfl⟩
    rw [singleton_ratio_of_equal_energy A hE p i he]
    exact residual_ratio_antitone he hposi hmaxpos hle

lemma equal_energy_filters_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (p : Fin n) (he : 0 < colInner A p p) :
    (incrementCandidates A {p}).filter (fun j =>
        incrementRatio A {p} j = incrementBest A {p}) =
      (unused {p}).filter (fun j =>
        residualSq A {p} j = maxResidual A {p} ∧ 0 < residualSq A {p} j) := by
  by_cases hs : (incrementCandidates A {p}).Nonempty
  · have hbest := equal_energy_incrementBest A hE p he hs
    have hmaxpos : 0 < maxResidual A {p} := by
      obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup' hs (residualSq A {p})
      have hres : residualSq A {p} j = maxResidual A {p} := by
        rw [← hjsup, maxResidual_eq_candidate_sup A {p} hs]
      rw [← hres]
      exact (mem_filter.mp hj).2
    ext j
    constructor
    · intro hj
      have hmem := (mem_filter.mp hj).1
      have hr := (mem_filter.mp hj).2
      have hpos : 0 < residualSq A {p} j := (mem_filter.mp hmem).2
      have hratio := singleton_ratio_of_equal_energy A hE p j he
      have hle : residualSq A {p} j ≤ maxResidual A {p} := by
        rw [maxResidual_eq_candidate_sup A {p} hs, le_sup'_iff]
        exact ⟨j, hmem, le_rfl⟩
      have heqres : residualSq A {p} j = maxResidual A {p} := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · have hstrict := residual_ratio_strict_anti he hpos hmaxpos hlt
          exact absurd (hratio.symm.trans (hr.trans hbest)) (ne_of_lt hstrict).symm
        · exact heq
      exact mem_filter.mpr ⟨(mem_filter.mp hmem).1, heqres, hpos⟩
    · intro hj
      have hunused := (mem_filter.mp hj).1
      have hres := (mem_filter.mp hj).2.1
      have hpos := (mem_filter.mp hj).2.2
      have hmem : j ∈ incrementCandidates A {p} := mem_filter.mpr ⟨hunused, hpos⟩
      refine mem_filter.mpr ⟨hmem, ?_⟩
      rw [singleton_ratio_of_equal_energy A hE p j he, hbest, hres]
  · have hempty : incrementCandidates A {p} = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [hempty, filter_empty]
    symm
    refine eq_empty_of_forall_notMem ?_
    intro j hj
    have hpos := (mem_filter.mp hj).2.2
    have hmem : j ∈ incrementCandidates A {p} :=
      mem_filter.mpr ⟨(mem_filter.mp hj).1, hpos⟩
    simp [hempty] at hmem

theorem equal_energy_singleton_same_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (p : Fin n) (he : 0 < colInner A p p)
    (hG : (selectedColGram A {p}).det ≠ 0) :
    incrementPivot A {p} = cpqrPivot A {p} := by
  have hfilter := equal_energy_filters_eq A hE p he
  simp only [incrementPivot, cpqrPivot, if_neg hG, hfilter]

lemma equal_energy_first_pivot {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 2 ≤ k) (hn : 0 < n) :
    cpqrPivot A ∅ = some ⟨0, hn⟩ := by
  set z : Fin n := ⟨0, hn⟩
  have he : ∀ j : Fin n, residualSq A ∅ j = (k : ℝ) / n := by
    intro j
    rw [← colInner_eq_residualSq, equal_column_energy A hA hE hn j]
  have hpos : ∀ j : Fin n, 0 < residualSq A ∅ j := by
    intro j
    rw [he]
    exact div_pos (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hn)
  have hmax : maxResidual A ∅ = (k : ℝ) / n := by
    have hne : (unused (∅ : Finset (Fin n))).Nonempty := ⟨z, by simp [unused]⟩
    rw [maxResidual, dif_pos hne]
    apply le_antisymm
    · rw [sup'_le_iff]
      intro j _
      rw [he]
    · rw [le_sup'_iff]
      refine ⟨z, by simp [unused], ?_⟩
      rw [he]
  have hfilter :
      (unused (∅ : Finset (Fin n))).filter
        (fun j => residualSq A ∅ j = maxResidual A ∅ ∧ 0 < residualSq A ∅ j) =
        univ := by
    ext j
    constructor
    · intro _
      exact mem_univ _
    · intro _
      have hunused : j ∈ unused (∅ : Finset (Fin n)) := by simp [unused]
      have heq : residualSq A ∅ j = maxResidual A ∅ := by rw [he, hmax]
      exact mem_filter.mpr ⟨hunused, heq, hpos j⟩
  unfold cpqrPivot
  rw [hfilter]
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨z, mem_univ _⟩
  rw [dif_pos hne]
  congr 1
  rw [min'_eq_iff]
  refine ⟨mem_univ _, ?_⟩
  intro b _
  rw [Fin.le_iff_val_le_val]
  exact Nat.zero_le _

theorem equal_energy_cpqr_prefix_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 2 ≤ k) (hn : 0 < n) :
    cpqrPivot A ∅ = some ⟨0, hn⟩ ∧
    cpqrPivot A {⟨0, hn⟩} = incrementPivot A {⟨0, hn⟩} ∧
    (selectedColGram A (cpqrIterate A 2)).det ≠ 0 ∧
    ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
      (2 : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) := by
  set z : Fin n := ⟨0, hn⟩
  have hfirst := equal_energy_first_pivot A hA hE hk hn
  have hez : colInner A z z = (k : ℝ) / n := equal_column_energy A hA hE hn z
  have hepos : 0 < colInner A z z := by
    rw [hez]
    exact div_pos (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hn)
  have hdet : (selectedColGram A {z}).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero A z (by
      rw [← colInner_eq_residualSq]
      exact hepos)
  have hsame := (equal_energy_singleton_same_pivot A hE z hepos hdet).symm
  have hJcard : ({z} : Finset (Fin n)).card = 1 := card_singleton z
  have hcard : ({z} : Finset (Fin n)).card < k := by
    rw [hJcard]
    omega
  have htrace : ((selectedColGram A {z})⁻¹).trace = (n : ℝ) / k := by
    let B : Matrix (Fin ({z} : Finset (Fin n)).card)
        (Fin ({z} : Finset (Fin n)).card) ℝ :=
      fun _ _ => (colInner A z z)⁻¹
    have hinv : (selectedColGram A {z})⁻¹ = B := by
      simpa [B] using singleton_gram_inv A z (ne_of_gt hepos)
    rw [hinv, Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [sum_singletonIdx z]
    simp only [B]
    rw [hez, inv_div]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hpoly : (1 : ℝ) * ((n : ℝ) - 1 + 1) / ((k : ℝ) - 1 + 1) = (n : ℝ) / k := by
    field_simp [hk0]
    ring
  have hf : ((selectedColGram A {z})⁻¹).trace ≤
      (({z} : Finset (Fin n)).card : ℝ) *
        ((n : ℝ) - ({z} : Finset (Fin n)).card + 1) /
        ((k : ℝ) - ({z} : Finset (Fin n)).card + 1) := by
    have hrhs :
        (({z} : Finset (Fin n)).card : ℝ) *
          ((n : ℝ) - ({z} : Finset (Fin n)).card + 1) /
          ((k : ℝ) - ({z} : Finset (Fin n)).card + 1) =
        (1 : ℝ) * ((n : ℝ) - 1 + 1) / ((k : ℝ) - 1 + 1) := by
      rw [hJcard, Nat.cast_one]
    rw [hrhs, hpoly, htrace]
  obtain ⟨j0, hj0, hpos0, hr0⟩ := best_column_increment_le A hA {z} hdet hcard
  have hmem0 : j0 ∈ incrementCandidates A {z} :=
    mem_filter.mpr ⟨by simp [unused, hj0], hpos0⟩
  have hs : (incrementCandidates A {z}).Nonempty := ⟨j0, hmem0⟩
  have hfilter_ne :
      ((incrementCandidates A {z}).filter fun j =>
        incrementRatio A {z} j = incrementBest A {z}).Nonempty := by
    have hmem_img := min'_mem
      ((incrementCandidates A {z}).image (incrementRatio A {z})) (hs.image _)
    obtain ⟨j, hj, hjratio⟩ := mem_image.mp hmem_img
    refine ⟨j, mem_filter.mpr ⟨hj, ?_⟩⟩
    unfold incrementBest
    rw [dif_pos hs]
    exact hjratio
  set t := (incrementCandidates A {z}).filter fun j =>
    incrementRatio A {z} j = incrementBest A {z}
  have hP : incrementPivot A {z} = some (t.min' hfilter_ne) := by
    unfold incrementPivot
    rw [if_neg hdet]
    simp only [t]
    rw [dif_pos hfilter_ne]
  set j : Fin n := t.min' hfilter_ne
  have hmem : j ∈ t := min'_mem _ hfilter_ne
  have hratio_eq : incrementRatio A {z} j = incrementBest A {z} :=
    (mem_filter.mp hmem).2
  have hpos : 0 < residualSq A {z} j :=
    (mem_filter.mp (mem_filter.mp hmem).1).2
  have hjn : j ∉ ({z} : Finset (Fin n)) := by
    have hunused : j ∈ unused ({z} : Finset (Fin n)) :=
      (mem_filter.mp (mem_filter.mp hmem).1).1
    rw [unused] at hunused
    exact (mem_sdiff.mp hunused).2
  have hr0' : incrementRatio A {z} j0 ≤
      (((n : ℝ) - ({z} : Finset (Fin n)).card) +
          ((selectedColGram A {z})⁻¹).trace -
        ({z} : Finset (Fin n)).card) /
        ((k : ℝ) - ({z} : Finset (Fin n)).card) := by
    simpa [incrementRatio] using hr0
  have hratio_le : incrementRatio A {z} j ≤
      (((n : ℝ) - ({z} : Finset (Fin n)).card) +
          ((selectedColGram A {z})⁻¹).trace -
        ({z} : Finset (Fin n)).card) /
        ((k : ℝ) - ({z} : Finset (Fin n)).card) :=
    le_trans (by rw [hratio_eq]; exact incrementBest_le A {z} hmem0) hr0'
  have hstep := increment_insert_of_ratio A {z} hdet hcard hf hjn hpos hratio_le
  have hcpqr : cpqrPivot A {z} = some j := by
    rw [hsame, hP]
  have h0 : cpqrIterate A 0 = (∅ : Finset (Fin n)) := rfl
  have h1 : cpqrIterate A 1 = ({z} : Finset (Fin n)) := by
    conv_lhs => unfold cpqrIterate
    rw [h0, hfirst]
    rfl
  have h2 : cpqrIterate A 2 = insert j ({z} : Finset (Fin n)) := by
    conv_lhs => unfold cpqrIterate
    rw [h1, hcpqr]
  refine ⟨hfirst, hsame, ?_, ?_⟩
  · rw [h2]
    exact hstep.1
  · have hbound := hstep.2
    have hrhs :
        ((({z} : Finset (Fin n)).card : ℝ) + 1) *
          ((n : ℝ) - ({z} : Finset (Fin n)).card) /
          ((k : ℝ) - ({z} : Finset (Fin n)).card) =
        (2 : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) - 1) := by
      rw [hJcard, Nat.cast_one]
      norm_num
    rw [hrhs] at hbound
    rw [h2]
    exact hbound

lemma singleton_residual_of_equal_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (p j : Fin n) (he : 0 < colInner A p p) :
    residualSq A {p} j =
      colInner A p p - colInner A p j ^ 2 / colInner A p p := by
  have hGdet : (selectedColGram A {p}).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero A p (by
      rw [← colInner_eq_residualSq]
      exact he)
  have hv : (fun i => A i j) ⬝ᵥ (fun i => A i j) = colInner A j j := rfl
  rw [residualSq_eq_schur A {p} j hGdet, hv, hE j p, singleton_proj A p j (ne_of_gt he)]

lemma energy_sub_abs_ge_half_residual {e s r : ℝ}
    (he : 0 < e) (hr : r = e - s ^ 2 / e) (hr0 : 0 ≤ r) :
    r / 2 ≤ e - |s| := by
  have hmul : r * e = e ^ 2 - s ^ 2 := by
    rw [hr]
    field_simp [ne_of_gt he]
  have hprod : (e - |s|) * (e + |s|) = e ^ 2 - s ^ 2 := by
    calc
      (e - |s|) * (e + |s|) = e ^ 2 - |s| ^ 2 := by ring
      _ = e ^ 2 - s ^ 2 := by rw [sq_abs]
  have hsle : |s| ≤ e := by
    have hsq : s ^ 2 ≤ e ^ 2 := by nlinarith [hmul, hr0, he.le]
    exact abs_le_of_sq_le_sq hsq he.le
  have hr' : r = (e - |s|) * (e + |s|) / e :=
    (eq_div_iff (ne_of_gt he)).mpr (hmul.trans hprod.symm)
  have hgap : 0 ≤ e - |s| := sub_nonneg.mpr hsle
  rw [hr', div_div, div_le_iff₀ (mul_pos he (by norm_num : (0 : ℝ) < 2))]
  exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg s]) hgap

lemma rayleigh_fin_two {e s x0 x1 : ℝ} :
    (e - |s|) * (x0 ^ 2 + x1 ^ 2) ≤
      e * (x0 ^ 2 + x1 ^ 2) + 2 * s * x0 * x1 := by
  rcases le_total s 0 with hs | hs
  · rw [abs_of_nonpos hs]
    have : 0 ≤ -s * (x0 - x1) ^ 2 := mul_nonneg (neg_nonneg.mpr hs) (sq_nonneg _)
    nlinarith
  · rw [abs_of_nonneg hs]
    have : 0 ≤ s * (x0 + x1) ^ 2 := mul_nonneg hs (sq_nonneg _)
    nlinarith

lemma selectedColGram_apply_inner {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (a b : Fin J.card) :
    selectedColGram A J a b =
      colInner A (J.orderEmbOfFin rfl a) (J.orderEmbOfFin rfl b) := by
  simp only [selectedColGram, Matrix.mul_apply, Matrix.transpose_apply, selectedCols,
    Matrix.submatrix_apply, colInner, id_eq]

lemma sum_card_two {m : ℕ} (hm : m = 2) (f : Fin m → ℝ) :
    ∑ i : Fin m, f i = f (Fin.cast hm.symm 0) + f (Fin.cast hm.symm 1) := by
  subst hm
  simp [Fin.sum_univ_two, Fin.cast]

theorem equal_energy_cpqr_prefix_rayleigh {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hE : ∀ i j : Fin n, colInner A i i = colInner A j j)
    (hk : 2 ≤ k) (hn : 0 < n)
    (x : Fin (cpqrIterate A 2).card → ℝ) :
    ((k : ℝ) - 1) / (2 * ((n : ℝ) - 1)) * vecEnergy x ≤
      vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x) := by
  set z : Fin n := ⟨0, hn⟩
  have hfirst := equal_energy_first_pivot A hA hE hk hn
  have hez : colInner A z z = (k : ℝ) / n := equal_column_energy A hA hE hn z
  have hepos : 0 < colInner A z z := by
    rw [hez]
    exact div_pos (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hn)
  have hn2 : 2 ≤ n := by
    have hkn := orthogonalRows_le A hA
    omega
  have hdet : (selectedColGram A {z}).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero A z (by
      rw [← colInner_eq_residualSq]
      exact hepos)
  have hcard1 : ({z} : Finset (Fin n)).card < n := by
    rw [card_singleton]
    omega
  have hmax : ((k : ℝ) - 1) / ((n : ℝ) - 1) ≤ maxResidual A {z} := by
    simpa [card_singleton, Nat.cast_one] using nextResidual_ge A hA {z} hdet hcard1
  have havgpos : 0 < ((k : ℝ) - 1) / ((n : ℝ) - 1) := by
    have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
      linarith
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      linarith
    exact div_pos hk1 hn1
  have hmaxpos : 0 < maxResidual A {z} := lt_of_lt_of_le havgpos hmax
  have hunused : (unused ({z} : Finset (Fin n))).Nonempty := by
    refine card_pos.mp ?_
    have : 0 < n - 1 := by omega
    simpa [unused_card, card_singleton] using this
  obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_sup' hunused (residualSq A {z})
  have hmaxeq : maxResidual A {z} = residualSq A {z} j0 := by
    unfold maxResidual
    rw [dif_pos hunused]
    exact hj0eq
  have hpos0 : 0 < residualSq A {z} j0 := by
    rw [← hmaxeq]
    exact hmaxpos
  let s := (unused ({z} : Finset (Fin n))).filter fun j =>
    residualSq A {z} j = maxResidual A {z} ∧ 0 < residualSq A {z} j
  have hs : s.Nonempty := by
    refine ⟨j0, mem_filter.mpr ⟨hj0, ?_, hpos0⟩⟩
    rw [hmaxeq]
  have hP : cpqrPivot A {z} = some (s.min' hs) := by
    unfold cpqrPivot
    simp only [s]
    rw [dif_pos hs]
  set j : Fin n := s.min' hs
  have hmem : j ∈ s := min'_mem _ hs
  have hresj : residualSq A {z} j = maxResidual A {z} := (mem_filter.mp hmem).2.1
  have hposj : 0 < residualSq A {z} j := (mem_filter.mp hmem).2.2
  have hjn : j ∉ ({z} : Finset (Fin n)) := by
    have hunused : j ∈ unused ({z} : Finset (Fin n)) := (mem_filter.mp hmem).1
    rw [unused] at hunused
    exact (mem_sdiff.mp hunused).2
  have hzlt : z < j := by
    refine lt_of_le_of_ne ?_ ?_
    · simp [z, Fin.le_def]
    · intro h
      exact hjn (mem_singleton.mpr h.symm)
  let J : Finset (Fin n) := insert j ({z} : Finset (Fin n))
  have hJcard : J.card = 2 := by
    rw [card_insert_of_notMem hjn, card_singleton]
  have h0 : cpqrIterate A 0 = (∅ : Finset (Fin n)) := rfl
  have h1 : cpqrIterate A 1 = ({z} : Finset (Fin n)) := by
    conv_lhs => unfold cpqrIterate
    rw [h0, hfirst]
    rfl
  have h2 : cpqrIterate A 2 = J := by
    conv_lhs => unfold cpqrIterate
    rw [h1, hP]
  revert x
  rw [h2]
  intro x
  have hzcard : 0 < J.card := by
    rw [hJcard]
    exact Nat.zero_lt_two
  let i0 : Fin J.card := Fin.cast hJcard.symm 0
  let i1 : Fin J.card := Fin.cast hJcard.symm 1
  have hi0 : i0 = ⟨0, hzcard⟩ := Fin.ext (by simp [i0, Fin.cast])
  have hembed0 : J.orderEmbOfFin rfl i0 = J.min' (card_pos.mp hzcard) := by
    simpa [hi0] using orderEmbOfFin_zero (s := J) rfl hzcard
  have hmin : J.min' (card_pos.mp hzcard) = z := by
    rw [min'_eq_iff]
    refine ⟨mem_insert.mpr (Or.inr (mem_singleton_self _)), ?_⟩
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact le_of_lt hzlt
    · rw [mem_singleton.mp hb]
  have hlast : J.orderEmbOfFin rfl ⟨J.card - 1, Nat.sub_lt hzcard (Nat.succ_pos 0)⟩ =
      J.max' (card_pos.mp hzcard) :=
    orderEmbOfFin_last (s := J) rfl hzcard
  have hi1 : (⟨J.card - 1, Nat.sub_lt hzcard (Nat.succ_pos 0)⟩ : Fin J.card) = i1 := by
    apply Fin.ext
    simp [i1, Fin.cast, hJcard]
  have hembed1 : J.orderEmbOfFin rfl i1 = J.max' (card_pos.mp hzcard) := by
    simpa [hi1] using hlast
  have hmaxj : J.max' (card_pos.mp hzcard) = j := by
    rw [max'_eq_iff]
    refine ⟨mem_insert_self _ _, ?_⟩
    intro b hb
    rcases mem_insert.mp hb with rfl | hb
    · exact le_rfl
    · rw [mem_singleton.mp hb]
      exact le_of_lt hzlt
  have hsum2 (f : Fin J.card → ℝ) : ∑ i, f i = f i0 + f i1 := by
    simpa [i0, i1] using sum_card_two hJcard f
  set G := selectedColGram A J
  set e : ℝ := colInner A z z
  set sᵢ : ℝ := colInner A z j
  have hG00 : G i0 i0 = e := by
    unfold G
    rw [selectedColGram_apply_inner, hembed0, hmin]
  have hG11 : G i1 i1 = e := by
    unfold G
    rw [selectedColGram_apply_inner, hembed1, hmaxj, equal_column_energy A hA hE hn j, ← hez]
  have hG01 : G i0 i1 = sᵢ := by
    unfold G
    rw [selectedColGram_apply_inner, hembed0, hmin, hembed1, hmaxj]
  have hG10 : G i1 i0 = sᵢ := by
    unfold G
    rw [selectedColGram_apply_inner, hembed1, hmaxj, hembed0, hmin, colInner_comm]
  have hmul (i : Fin J.card) :
      (G *ᵥ x) i = G i i0 * x i0 + G i i1 * x i1 := by
    rw [Matrix.mulVec_apply_eq_sum, hsum2]
  have hdot : x ⬝ᵥ (G *ᵥ x) =
      x i0 * (G *ᵥ x) i0 + x i1 * (G *ᵥ x) i1 := by
    rw [dotProduct, hsum2]
  have hexpand : x ⬝ᵥ (G *ᵥ x) =
      e * (x i0 ^ 2 + x i1 ^ 2) + 2 * sᵢ * x i0 * x i1 := by
    rw [hdot, hmul, hmul, hG00, hG11, hG01, hG10]
    ring
  have hvx : vecEnergy x = x i0 ^ 2 + x i1 ^ 2 := by
    rw [vecEnergy, hsum2]
  have hray := rayleigh_fin_two (e := e) (s := sᵢ) (x0 := x i0) (x1 := x i1)
  have hform : (e - |sᵢ|) * vecEnergy x ≤ x ⬝ᵥ (G *ᵥ x) := by
    rw [hexpand, hvx]
    exact hray
  have hres := singleton_residual_of_equal_energy A hE z j hepos
  have hhalf := energy_sub_abs_ge_half_residual hepos hres (residualSq_nonneg A {z} j)
  have hresge : ((k : ℝ) - 1) / ((n : ℝ) - 1) ≤ residualSq A {z} j := by
    rw [hresj]
    exact hmax
  have hgap : ((k : ℝ) - 1) / (2 * ((n : ℝ) - 1)) ≤ e - |sᵢ| := by
    have hdiv : ((k : ℝ) - 1) / (2 * ((n : ℝ) - 1)) =
        (((k : ℝ) - 1) / ((n : ℝ) - 1)) / 2 := by
      rw [div_div]
      congr 1
      ring
    rw [hdiv]
    exact le_trans (div_le_div_of_nonneg_right hresge (by norm_num)) hhalf
  have hscale : ((k : ℝ) - 1) / (2 * ((n : ℝ) - 1)) * vecEnergy x ≤
      (e - |sᵢ|) * vecEnergy x :=
    mul_le_mul_of_nonneg_right hgap (vecEnergy_nonneg x)
  have hquad : x ⬝ᵥ (G *ᵥ x) = vecEnergy (selectedCols A J *ᵥ x) :=
    (vecEnergy_selectedCols A J x).symm
  exact hscale.trans (hform.trans (le_of_eq hquad))

end StructuredColumnSelection
