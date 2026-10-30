import StructuredColumnSelection.EqualEnergyPivot
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-column Grams under leverage ratio and coherence

If orthogonal rows have leverage ratio at most `τ` and normalized coherence
at most `ρ < 1`, every two-column Gram is invertible and its inverse trace
is at most `2 τ² n / (k (1 - ρ²))`.

This bounds every pair. It does not bound a `k`-set for `k > 2`. It does
not close outcome 3. It is not a polynomial CPQR bound for every
orthogonal-row matrix. The census did not prove this.
`joint_pair_inv_trace` does not identify `cpqrIterate A 2`.

`joint_cpqr_prefix_trace` is the CPQR prefix of length 2 under the same
joint leverage-ratio and coherence hypothesis. It does not bound later
pivots. It does not close outcome 3. It is not a polynomial bound for
every orthogonal-row matrix.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma pairGram_inv_trace (a c b : ℝ) (_hd : a * b - c ^ 2 ≠ 0) :
    ((!![a, c; c, b])⁻¹).trace = (a + b) / (a * b - c ^ 2) := by
  have hdet : (Matrix.det !![a, c; c, b]) = a * b - c ^ 2 := by
    rw [det_fin_two_of, ← pow_two]
  rw [Matrix.inv_def, hdet, Ring.inverse_eq_inv, adjugate_fin_two_of, trace_smul,
    trace_fin_two_of, smul_eq_mul]
  conv_rhs => rw [div_eq_mul_inv, mul_comm, add_comm]

lemma column_energy_ratio_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hn : 1 ≤ n) {τ : ℝ} (hτ : 1 ≤ τ)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (j : Fin n) :
    (k : ℝ) / ((n : ℝ) * τ) ≤ residualSq A ∅ j := by
  have hsum := leverageSum A hA
  have hlarge : ∃ jmax : Fin n, (k : ℝ) / n ≤ residualSq A ∅ jmax := by
    by_contra h
    have hlt : ∀ t : Fin n, residualSq A ∅ t < (k : ℝ) / n :=
      fun t => not_le.mp ((not_exists.mp h) t)
    have hstrict :
        ∑ t : Fin n, residualSq A ∅ t < ∑ t : Fin n, (k : ℝ) / (n : ℝ) := by
      refine sum_lt_sum (fun t _ => (hlt t).le) ?_
      exact ⟨⟨0, by omega⟩, mem_univ _, hlt _⟩
    have hconst : ∑ t : Fin n, (k : ℝ) / (n : ℝ) = (k : ℝ) := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp [hn0]
    rw [hsum, hconst] at hstrict
    exact lt_irrefl _ hstrict
  obtain ⟨jmax, hjmax⟩ := hlarge
  have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
  have hdiv : residualSq A ∅ jmax / τ ≤ residualSq A ∅ j :=
    (div_le_iff₀ hτpos).mpr (by simpa [mul_comm] using hlev jmax j)
  have hscale : ((k : ℝ) / n) / τ ≤ residualSq A ∅ jmax / τ :=
    div_le_div_of_nonneg_right hjmax hτpos.le
  have hrewrite : ((k : ℝ) / n) / τ = (k : ℝ) / ((n : ℝ) * τ) :=
    div_div (k : ℝ) (n : ℝ) τ
  exact (hrewrite ▸ hscale).trans hdiv

lemma pair_coherence_sq {a b c ρ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ0 : 0 ≤ ρ)
    (hc : |c| ≤ ρ * Real.sqrt a * Real.sqrt b) :
    c ^ 2 ≤ ρ ^ 2 * a * b := by
  have hright : 0 ≤ ρ * Real.sqrt a * Real.sqrt b := by positivity
  have hsq : c ^ 2 ≤ (ρ * Real.sqrt a * Real.sqrt b) ^ 2 :=
    (sq_le_sq).2 (by rwa [abs_of_nonneg hright])
  have hexp : (ρ * Real.sqrt a * Real.sqrt b) ^ 2 = ρ ^ 2 * a * b := by
    calc
      (ρ * Real.sqrt a * Real.sqrt b) ^ 2
          = (ρ * Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2 := by rw [mul_pow]
      _ = ρ ^ 2 * (Real.sqrt a) ^ 2 * (Real.sqrt b) ^ 2 := by rw [mul_pow]
      _ = ρ ^ 2 * a * b := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
  exact le_trans hsq (le_of_eq hexp)

lemma pair_det_pos {a b c ρ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hc : |c| ≤ ρ * Real.sqrt a * Real.sqrt b) :
    0 < a * b - c ^ 2 := by
  have hδ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  have hcsq := pair_coherence_sq ha.le hb.le hρ0 hc
  have hdetge : a * b * (1 - ρ ^ 2) ≤ a * b - c ^ 2 := by
    have hcsq' : c ^ 2 ≤ a * b * ρ ^ 2 := by
      calc
        c ^ 2 ≤ ρ ^ 2 * a * b := hcsq
        _ = a * b * ρ ^ 2 := by ring
    linarith
  have hleft : 0 < a * b * (1 - ρ ^ 2) := by positivity
  exact lt_of_lt_of_le hleft hdetge

lemma pair_ratio_le {a b c μ τ ρ : ℝ}
    (hμ : 0 < μ) (hτ : 0 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (ha : μ ≤ a) (hb : μ ≤ b) (haτ : a ≤ τ * μ) (hbτ : b ≤ τ * μ)
    (hc : |c| ≤ ρ * Real.sqrt a * Real.sqrt b) :
    (a + b) / (a * b - c ^ 2) ≤ (2 * τ) / (μ * (1 - ρ ^ 2)) := by
  have hδ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  have ha0 : 0 < a := lt_of_lt_of_le hμ ha
  have hb0 : 0 < b := lt_of_lt_of_le hμ hb
  have hdetpos := pair_det_pos ha0 hb0 hρ0 hρ hc
  have hcsq := pair_coherence_sq ha0.le hb0.le hρ0 hc
  have hdetge : a * b * (1 - ρ ^ 2) ≤ a * b - c ^ 2 := by
    have hcsq' : c ^ 2 ≤ a * b * ρ ^ 2 := by
      calc
        c ^ 2 ≤ ρ ^ 2 * a * b := hcsq
        _ = a * b * ρ ^ 2 := by ring
    linarith
  have hnum : a + b ≤ 2 * τ * μ := by linarith
  have hab : μ * μ ≤ a * b := mul_le_mul ha hb hμ.le ha0.le
  have hden : μ * μ * (1 - ρ ^ 2) ≤ a * b - c ^ 2 := by
    have hscale : μ * μ * (1 - ρ ^ 2) ≤ a * b * (1 - ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hab hδ.le
    exact hscale.trans hdetge
  have hstep1 : (a + b) / (a * b - c ^ 2) ≤ (2 * τ * μ) / (a * b - c ^ 2) :=
    div_le_div_of_nonneg_right hnum hdetpos.le
  have hdenpos : 0 < μ * μ * (1 - ρ ^ 2) := by positivity
  have hstep2 :
      (2 * τ * μ) / (a * b - c ^ 2) ≤ (2 * τ * μ) / (μ * μ * (1 - ρ ^ 2)) :=
    div_le_div_of_nonneg_left (by positivity) hdenpos hden
  have hsimp : (2 * τ * μ) / (μ * μ * (1 - ρ ^ 2)) = (2 * τ) / (μ * (1 - ρ ^ 2)) := by
    have hμ0 : μ ≠ 0 := ne_of_gt hμ
    have hδ0 : 1 - ρ ^ 2 ≠ 0 := ne_of_gt hδ
    field_simp [hμ0, hδ0]
  exact hstep1.trans (hstep2.trans_eq hsimp)

theorem joint_pair_inv_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 1 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    ∀ i j : Fin n, i ≠ j →
      (selectedColGram A {i, j}).det ≠ 0 ∧
        ((selectedColGram A {i, j})⁻¹).trace ≤
          (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
  intro i j hij
  let J : Finset (Fin n) := {i, j}
  have hcard : J.card = 2 := by simpa [J] using Finset.card_pair hij
  let e : Fin 2 ≃ Fin J.card := finCongr hcard.symm
  let p0 : Fin n := J.orderEmbOfFin rfl (e 0)
  let p1 : Fin n := J.orderEmbOfFin rfl (e 1)
  have hpne : p0 ≠ p1 := by
    intro h
    have hval : (e (0 : Fin 2) : ℕ) = e 1 :=
      congrArg Fin.val ((J.orderEmbOfFin rfl).injective h)
    simp [e, finCongr_apply] at hval
  obtain ⟨jmin, _, hjmin⟩ :=
    exists_min_image (univ : Finset (Fin n)) (residualSq A ∅) ⟨i, mem_univ _⟩
  let μ : ℝ := residualSq A ∅ jmin
  have hκ : (k : ℝ) / ((n : ℝ) * τ) ≤ μ :=
    column_energy_ratio_ge A hA hn hτ hlev jmin
  have hκpos : 0 < (k : ℝ) / ((n : ℝ) * τ) := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
    exact div_pos hkpos (mul_pos hnpos hτpos)
  have hμpos : 0 < μ := lt_of_lt_of_le hκpos hκ
  let ℓ0 : ℝ := residualSq A ∅ p0
  let ℓ1 : ℝ := residualSq A ∅ p1
  let c : ℝ := colInner A p0 p1
  have hℓ0μ : μ ≤ ℓ0 := hjmin p0 (mem_univ _)
  have hℓ1μ : μ ≤ ℓ1 := hjmin p1 (mem_univ _)
  have hℓ0τ : ℓ0 ≤ τ * μ := hlev p0 jmin
  have hℓ1τ : ℓ1 ≤ τ * μ := hlev p1 jmin
  have hc : |c| ≤ ρ * Real.sqrt ℓ0 * Real.sqrt ℓ1 := hcoh p0 p1 hpne
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hratio :=
    pair_ratio_le hμpos hτ0 hρ0 hρ hℓ0μ hℓ1μ hℓ0τ hℓ1τ hc
  have hδ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  have hμstep :
      (2 * τ) / (μ * (1 - ρ ^ 2)) ≤
        (2 * τ) / (((k : ℝ) / ((n : ℝ) * τ)) * (1 - ρ ^ 2)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hκpos hδ)
      (mul_le_mul_of_nonneg_right hκ hδ.le)
  have heq :
      (2 * τ) / (((k : ℝ) / ((n : ℝ) * τ)) * (1 - ρ ^ 2)) =
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hτne : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hτ)
    have hδ0 : 1 - ρ ^ 2 ≠ 0 := ne_of_gt hδ
    field_simp [hn0, hk0, hτne, hδ0]
  have hdetpos : 0 < ℓ0 * ℓ1 - c ^ 2 :=
    pair_det_pos (lt_of_lt_of_le hμpos hℓ0μ) (lt_of_lt_of_le hμpos hℓ1μ) hρ0 hρ hc
  have hcast :
      ((selectedCols A J)ᵀ * selectedCols A J).submatrix e e = !![ℓ0, c; c, ℓ1] := by
    ext p q
    rw [submatrix_apply, show (selectedCols A J)ᵀ * selectedCols A J =
      selectedColGram A J from rfl, selectedColGram_apply_inner]
    fin_cases p <;> fin_cases q
    · rw [colInner_eq_residualSq]
      rfl
    · rfl
    · rw [colInner_comm]
      rfl
    · rw [colInner_eq_residualSq]
      rfl
  have hGdet : (selectedColGram A J).det ≠ 0 := by
    have hdeteq : (selectedColGram A J).det = ℓ0 * ℓ1 - c ^ 2 := by
      rw [show selectedColGram A J = (selectedCols A J)ᵀ * selectedCols A J from rfl,
        ← det_submatrix_equiv_self e, hcast, det_fin_two_of, ← pow_two]
    rw [hdeteq]
    exact ne_of_gt hdetpos
  have hsub :
      ((selectedCols A J).submatrix id e)ᵀ * (selectedCols A J).submatrix id e =
        ((selectedCols A J)ᵀ * selectedCols A J).submatrix e e := by
    ext p q
    simp only [mul_apply, transpose_apply, submatrix_apply, id_eq]
  have htrace_eq :
      ((selectedColGram A J)⁻¹).trace = (ℓ0 + ℓ1) / (ℓ0 * ℓ1 - c ^ 2) := by
    have hre := gram_inv_trace_reindex (selectedCols A J) e hGdet
    rw [hsub, hcast, pairGram_inv_trace ℓ0 c ℓ1 (ne_of_gt hdetpos)] at hre
    exact hre.symm
  refine ⟨?_, ?_⟩
  · simpa [J] using hGdet
  · have hle : (ℓ0 + ℓ1) / (ℓ0 * ℓ1 - c ^ 2) ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) :=
      hratio.trans (hμstep.trans heq.le)
    rw [← htrace_eq] at hle
    simpa [J] using hle

/-- The CPQR prefix of length 2 under the joint leverage-ratio and
coherence hypothesis. It does not bound later pivots. It does not close
outcome 3. It is not a polynomial bound for every orthogonal-row matrix. -/
theorem joint_cpqr_prefix_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    ∃ j0 j1 : Fin n, j0 ≠ j1 ∧
      cpqrIterate A 2 = {j0, j1} ∧
      (selectedColGram A (cpqrIterate A 2)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
  have hn1 : 1 ≤ n := by omega
  have hsum := leverageSum A hA
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hsome : ∃ j : Fin n, 0 < residualSq A ∅ j := by
    by_contra hnone
    have hle : ∀ j : Fin n, residualSq A ∅ j ≤ 0 :=
      fun j => not_lt.mp ((not_exists.mp hnone) j)
    have hzero : ∑ j : Fin n, residualSq A ∅ j = 0 := by
      refine Finset.sum_eq_zero fun j _ => residualSq_eq_zero_of_nonpos A ∅ j (hle j)
    rw [hsum] at hzero
    exact hkpos.ne' hzero
  have hempty : ∃ j ∈ unused (∅ : Finset (Fin n)), 0 < residualSq A ∅ j := by
    obtain ⟨j, hj⟩ := hsome
    exact ⟨j, by simp [unused], hj⟩
  obtain ⟨j0, hj0⟩ := cpqrPivot_exists_of_pos A hempty
  have hpos0 : 0 < residualSq A ∅ j0 := (cpqrPivot_spec hj0).2.2
  have hG0 : (selectedColGram A {j0}).det ≠ 0 :=
    selectedColGram_singleton_det_ne_zero A j0 hpos0
  have he0 : colInner A j0 j0 ≠ 0 := by
    rw [colInner_eq_residualSq]
    exact hpos0.ne'
  have hdet0 : (selectedColGram A {j0}).det = residualSq A ∅ j0 := by
    have hmul := residualSq_mul_gram A (J := (∅ : Finset (Fin n))) (j := j0)
      (notMem_empty _) (Or.inl card_empty)
    rw [if_pos card_empty, mul_one] at hmul
    have hsing : insert j0 (∅ : Finset (Fin n)) = {j0} := by
      ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · rintro (rfl | hx)
        · rfl
        · exact (notMem_empty x hx).elim
      · exact Or.inl
    rw [hsing] at hmul
    exact Eq.symm hmul
  have hres_pos : ∀ j : Fin n, j ≠ j0 → 0 < residualSq A {j0} j := by
    intro j hj
    have hschur : residualSq A {j0} j =
        residualSq A ∅ j - colInner A j0 j ^ 2 / residualSq A ∅ j0 := by
      have hdot : (fun i => A i j) ⬝ᵥ (fun i => A i j) = ∑ i, A i j * A i j := rfl
      have hinner : colInner A j j = ∑ i, A i j * A i j := rfl
      rw [residualSq_eq_schur A {j0} j hG0, singleton_proj A j0 j he0, hdot, ← hinner,
        colInner_eq_residualSq A j, colInner_eq_residualSq A j0]
    have hnotin : j ∉ ({j0} : Finset (Fin n)) := by
      simpa [mem_singleton] using hj
    have hmul := residualSq_mul_gram A hnotin (Or.inr hG0)
    have hcard1 : ({j0} : Finset (Fin n)).card ≠ 0 := by
      rw [card_singleton]
      exact one_ne_zero
    have hinsert : insert j ({j0} : Finset (Fin n)) = {j0, j} := by
      ext x
      simp only [mem_insert, mem_singleton]
      rw [or_comm]
    rw [if_neg hcard1, hdet0, hinsert] at hmul
    have hquot : residualSq A {j0} j =
        (selectedColGram A {j0, j}).det / residualSq A ∅ j0 :=
      (eq_div_iff hpos0.ne').2 hmul
    have hschur_eq :
        residualSq A ∅ j - colInner A j0 j ^ 2 / residualSq A ∅ j0 =
          (selectedColGram A {j0, j}).det / residualSq A ∅ j0 := by
      rw [← hschur, hquot]
    have hdet_ne :=
      (joint_pair_inv_trace A hA hk hn1 τ ρ hτ hρ0 hρ hlev hcoh j0 j hj.symm).1
    have hdet_nn : 0 ≤ (selectedColGram A {j0, j}).det := by
      simpa [selectedColGram] using det_colGram_nonneg (selectedCols A {j0, j})
    have hdet_pos : 0 < (selectedColGram A {j0, j}).det :=
      lt_of_le_of_ne hdet_nn hdet_ne.symm
    rw [hschur, hschur_eq]
    exact div_pos hdet_pos hpos0
  have hex : ∃ j : Fin n, j ≠ j0 := by
    by_cases hzero : j0 = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      rw [hzero] at h
      have : (1 : ℕ) = 0 := by simpa using congrArg Fin.val h
      omega
    · exact ⟨⟨0, by omega⟩, Ne.symm hzero⟩
  have hpos_unused : ∃ j ∈ unused ({j0} : Finset (Fin n)),
      0 < residualSq A {j0} j := by
    obtain ⟨j, hj⟩ := hex
    refine ⟨j, ?_, hres_pos j hj⟩
    simp [unused, mem_singleton, hj]
  obtain ⟨j1, hj1⟩ := cpqrPivot_exists_of_pos A hpos_unused
  have hjne : j0 ≠ j1 := by
    intro h
    have hnot : j1 ∉ ({j0} : Finset (Fin n)) := (cpqrPivot_spec hj1).1
    exact hnot (mem_singleton.mpr h.symm)
  have h0 : cpqrIterate A 0 = (∅ : Finset (Fin n)) := rfl
  have h1 : cpqrIterate A 1 = ({j0} : Finset (Fin n)) := by
    conv_lhs => unfold cpqrIterate
    rw [h0, hj0]
    rfl
  have h2 : cpqrIterate A 2 = insert j1 ({j0} : Finset (Fin n)) := by
    conv_lhs => unfold cpqrIterate
    rw [h1, hj1]
  have hset : cpqrIterate A 2 = {j0, j1} := by
    rw [h2]
    ext x
    simp only [mem_insert, mem_singleton]
    rw [or_comm]
  have hpair := joint_pair_inv_trace A hA hk hn1 τ ρ hτ hρ0 hρ hlev hcoh j0 j1 hjne
  refine ⟨j0, j1, hjne, hset, ?_, ?_⟩
  · rw [hset]
    exact hpair.1
  · rw [hset]
    exact hpair.2

end StructuredColumnSelection
