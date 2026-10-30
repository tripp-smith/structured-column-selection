import StructuredColumnSelection.EqualEnergyPivot
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Finset.Max
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

`joint_cpqr_prefix_rayleigh` is the Rayleigh form of that length-2 prefix.
The coefficient is the reciprocal of the inverse-trace bound. It is not
sharp. It does not bound later pivots. It does not close outcome 3. It
is not a polynomial bound for every orthogonal-row matrix.

`joint_cpqr_three_trace` is the third CPQR pivot under the same joint
hypothesis, plus `3 ≤ k`. It does not bound pivots after the third. It
does not close outcome 3. It is not a polynomial bound for every
orthogonal-row matrix. The constant is not claimed sharp.

`joint_cpqr_k3` specializes that length-3 prefix to the full CPQR set
when `k = 3`. It is not a bound for general `k`. It does not close
outcome 3. It is not sharp.

`joint_cpqr_step` is one CPQR pivot step under a leverage-ratio bound,
assuming a trace bound on the current prefix. It moves length `t` to
length `t + 1`. It is not a bound on the full `k`-set. It is not a
polynomial bound. It does not close outcome 3. Coherence is not used.
The recurrence is not iterated here.

`joint_cpqr_step_tight` is tighter than `joint_cpqr_step` by one copy of
the current trace. Still one step. Not an iteration. Not a polynomial
bound. Does not close outcome 3. The new bound is not claimed sharp in
general.

`jointTraceBound` iterates that step from the length-2 bound up to any
`2 ≤ t ≤ k`. Each step multiplies the previous bound by
`1 + (τ k / n) (n - s) / (k - s)` and adds `(n - s) / (k - s)`. That
factor is `O(τ k)` near the last pivot. The bound is not a polynomial in
`k`. `joint_cpqr_trace_bound` records the iteration. It does not close
outcome 3. Coherence is used only at length 2.

`jointTraceBoundTight` iterates `joint_cpqr_step_tight` from that same
length-2 bound. The successor is `(1 + (τ k / n) B) (n - s) / (k - s)`
with no added copy of `B`. When `n = k`, each step sends `B` to
`1 + τ B`, so `τ > 1` is still exponential in the number of pivots.
When `n > k`, the factor `(n - s) / (k - s)` is not a polynomial bound.
The recurrence is not a polynomial in `k`.
`joint_cpqr_trace_bound_tight` records the iteration. It does not close
outcome 3. The loose recurrence `jointTraceBound` is unchanged. The
square equal-leverage closed form is unchanged.

`joint_square_equal_trace` is the full CPQR set on a square matrix with
equal column energies. The inverse trace is at most
`(k : ℝ) - 2 + 2 / (1 - ρ ^ 2)`. Square equal-leverage only. Not a
polynomial bound for rectangular or `τ > 1` matrices. Does not close
outcome 3. Not claimed sharp for `ρ > 0`. On the identity at `ρ = 0`
the bound equals `k`, and the inverse trace equals `k`.
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

lemma quadForm_submatrix_finCongr {t m : ℕ}
    (M : Matrix (Fin t) (Fin t) ℝ) (h : t = m) (x : Fin t → ℝ) :
    x ⬝ᵥ (M *ᵥ x) =
      (fun i : Fin m => x ((finCongr h.symm) i)) ⬝ᵥ
        ((M.submatrix (finCongr h.symm) (finCongr h.symm)) *ᵥ
          fun i : Fin m => x ((finCongr h.symm) i)) := by
  let e : Fin m ≃ Fin t := finCongr h.symm
  let y : Fin m → ℝ := fun i => x (e i)
  let M2 : Matrix (Fin m) (Fin m) ℝ := M.submatrix e e
  have hmul (i : Fin m) : (M *ᵥ x) (e i) = (M2 *ᵥ y) i := by
    rw [mulVec_apply_eq_sum, mulVec_apply_eq_sum]
    refine (Fintype.sum_equiv e
      (fun k => M2 i k * y k)
      (fun j => M (e i) j * x j) ?_).symm
    intro k
    simp [M2, y, Matrix.submatrix_apply]
  refine (Fintype.sum_equiv e
    (fun i => y i * (M2 *ᵥ y) i)
    (fun j => x j * (M *ᵥ x) j) ?_).symm
  intro i
  rw [hmul]

/-- For `H = !![a, c; c, b]` with positive diagonal and positive determinant,
`‖x‖² ≤ tr(H) · (xᵀ H⁻¹ x)`. The numerator of the difference is
`(b x₁ - c x₂)² + (a x₂ - c x₁)²`. -/
lemma symm_fin_two_spd_rayleigh (a c b : ℝ) (x : Fin 2 → ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (hdet : 0 < a * b - c ^ 2) :
    vecEnergy x ≤
      (!![a, c; c, b]).trace *
        (x ⬝ᵥ ((!![a, c; c, b])⁻¹ *ᵥ x)) := by
  set H : Matrix (Fin 2) (Fin 2) ℝ := !![a, c; c, b]
  set Δ : ℝ := a * b - c ^ 2
  have hΔ : 0 < Δ := hdet
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hHdet : H.det = Δ := by
    rw [show H = !![a, c; c, b] from rfl, det_fin_two_of]
    simp only [Δ, pow_two]
  set M : Matrix (Fin 2) (Fin 2) ℝ := !![b, -c; -c, a]
  have hinv : H⁻¹ = Δ⁻¹ • M := by
    rw [Matrix.inv_def, hHdet, Ring.inverse_eq_inv]
    simp [H, M]
  have h00 : M 0 0 = b := by simp [M]
  have h01 : M 0 1 = -c := by simp [M]
  have h10 : M 1 0 = -c := by simp [M]
  have h11 : M 1 1 = a := by simp [M]
  set x0 : ℝ := x 0
  set x1 : ℝ := x 1
  set Q : ℝ := b * x0 ^ 2 - 2 * c * x0 * x1 + a * x1 ^ 2
  have h0 : (M *ᵥ x) 0 = b * x0 - c * x1 := by
    rw [mulVec_apply_eq_sum, Fin.sum_univ_two, h00, h01]
    simp [x0, x1]
    ring
  have h1 : (M *ᵥ x) 1 = a * x1 - c * x0 := by
    rw [mulVec_apply_eq_sum, Fin.sum_univ_two, h10, h11]
    simp [x0, x1]
    ring
  have hdotM : x ⬝ᵥ (M *ᵥ x) = Q := by
    rw [dotProduct, Fin.sum_univ_two, h0, h1]
    simp [x0, x1, Q]
    ring
  have hquad : x ⬝ᵥ (H⁻¹ *ᵥ x) = Δ⁻¹ * Q := by
    rw [hinv, smul_mulVec, dotProduct_smul, smul_eq_mul, hdotM]
  have henergy : vecEnergy x = x0 ^ 2 + x1 ^ 2 := by
    rw [vecEnergy, Fin.sum_univ_two]
  have htrace : H.trace = a + b := by
    rw [show H = !![a, c; c, b] from rfl, trace_fin_two_of]
  have hnum : (a + b) * Q - Δ * (x0 ^ 2 + x1 ^ 2) =
      (b * x0 - c * x1) ^ 2 + (a * x1 - c * x0) ^ 2 := by
    simp only [Q, Δ]
    ring
  have hsplit : (a + b) * (Δ⁻¹ * Q) - (x0 ^ 2 + x1 ^ 2) =
      ((a + b) * Q - Δ * (x0 ^ 2 + x1 ^ 2)) / Δ := by
    field_simp [hΔne]
  have hdiff : (a + b) * (x ⬝ᵥ (H⁻¹ *ᵥ x)) - vecEnergy x =
      ((b * x0 - c * x1) ^ 2 + (a * x1 - c * x0) ^ 2) / Δ := by
    rw [hquad, henergy, hsplit, hnum]
  have hnn : 0 ≤ (b * x0 - c * x1) ^ 2 + (a * x1 - c * x0) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnonneg : 0 ≤ (a + b) * (x ⬝ᵥ (H⁻¹ *ᵥ x)) - vecEnergy x := by
    rw [hdiff]
    exact div_nonneg hnn hΔ.le
  have hle : vecEnergy x ≤ (a + b) * (x ⬝ᵥ (H⁻¹ *ᵥ x)) := by
    linarith
  simpa [htrace] using hle

/-- Rayleigh form of the length-2 CPQR prefix under the joint leverage-ratio
and coherence hypothesis. Not sharp. Does not bound later pivots. Does not
close outcome 3. Not a polynomial bound for every orthogonal-row matrix. -/
theorem joint_cpqr_prefix_rayleigh {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (x : Fin (cpqrIterate A 2).card → ℝ) :
    ((k : ℝ) * (1 - ρ ^ 2)) / ((2 : ℝ) * τ ^ 2 * (n : ℝ)) * vecEnergy x ≤
      vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x) := by
  let J : Finset (Fin n) := cpqrIterate A 2
  obtain ⟨j0, j1, hjne, hset, -, htr⟩ :=
    joint_cpqr_prefix_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh
  have hn1 : 1 ≤ n := by omega
  have hpair :=
    joint_pair_inv_trace A hA hk hn1 τ ρ hτ hρ0 hρ hlev hcoh j0 j1 hjne
  have hcard : J.card = 2 := by
    unfold J
    rw [hset]
    exact Finset.card_pair hjne
  let G : Matrix (Fin J.card) (Fin J.card) ℝ := selectedColGram A J
  have hGdet : G.det ≠ 0 := by
    unfold G J
    rw [hset]
    exact hpair.1
  have hdet_nn : 0 ≤ G.det := by
    unfold G selectedColGram
    exact det_colGram_nonneg (selectedCols A J)
  have hdet_pos : 0 < G.det := lt_of_le_of_ne hdet_nn (Ne.symm hGdet)
  let G2 : Matrix (Fin 2) (Fin 2) ℝ := selectedColGramCast A J hcard
  have hG2det_eq : G2.det = G.det := selectedColGramCast_det A J hcard
  have hG2pos : 0 < G2.det := by
    rw [hG2det_eq]
    exact hdet_pos
  let p0 : Fin n := J.orderEmbOfFin hcard 0
  let p1 : Fin n := J.orderEmbOfFin hcard 1
  let ℓ0 : ℝ := residualSq A ∅ p0
  let ℓ1 : ℝ := residualSq A ∅ p1
  let c : ℝ := colInner A p0 p1
  have h00 : G2 0 0 = ℓ0 := by
    unfold G2 ℓ0 p0
    rw [selectedColGramCast_apply, ← colInner_eq_residualSq]
    simp [colInner]
  have h11 : G2 1 1 = ℓ1 := by
    unfold G2 ℓ1 p1
    rw [selectedColGramCast_apply, ← colInner_eq_residualSq]
    simp [colInner]
  have h01 : G2 0 1 = c := by
    unfold G2 c p0 p1
    rw [selectedColGramCast_apply]
    simp [colInner]
  have h10 : G2 1 0 = c := by
    unfold G2 c p0 p1
    rw [selectedColGramCast_apply]
    change colInner A (J.orderEmbOfFin hcard 1) (J.orderEmbOfFin hcard 0) =
      colInner A (J.orderEmbOfFin hcard 0) (J.orderEmbOfFin hcard 1)
    exact colInner_comm A _ _
  have hG2 : G2 = !![ℓ0, c; c, ℓ1] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [h00]
    · simp [h01]
    · simp [h10]
    · simp [h11]
  set Δ : ℝ := ℓ0 * ℓ1 - c ^ 2
  have hΔeq : G2.det = Δ := by
    rw [hG2, det_fin_two_of]
    simp only [Δ, pow_two]
  have hΔpos : 0 < Δ := by
    rw [← hΔeq]
    exact hG2pos
  have hℓ0nn : 0 ≤ ℓ0 := residualSq_nonneg A ∅ p0
  have hℓ1nn : 0 ≤ ℓ1 := residualSq_nonneg A ∅ p1
  have hℓ0pos : 0 < ℓ0 := by
    by_contra hbad
    have hzero : ℓ0 = 0 := le_antisymm (not_lt.mp hbad) hℓ0nn
    have hle : Δ ≤ 0 := by
      have : Δ = -(c ^ 2) := by
        simp only [Δ, hzero]
        ring
      rw [this]
      exact neg_nonpos.mpr (sq_nonneg c)
    exact not_lt_of_ge hle hΔpos
  have hℓ1pos : 0 < ℓ1 := by
    by_contra hbad
    have hzero : ℓ1 = 0 := le_antisymm (not_lt.mp hbad) hℓ1nn
    have hle : Δ ≤ 0 := by
      have : Δ = -(c ^ 2) := by
        simp only [Δ, hzero]
        ring
      rw [this]
      exact neg_nonpos.mpr (sq_nonneg c)
    exact not_lt_of_ge hle hΔpos
  have hΔne : Δ ≠ 0 := ne_of_gt hΔpos
  set aH : ℝ := Δ⁻¹ * ℓ1
  set bH : ℝ := Δ⁻¹ * ℓ0
  set cH : ℝ := Δ⁻¹ * (-c)
  have haH : 0 < aH := mul_pos (inv_pos.mpr hΔpos) hℓ1pos
  have hbH : 0 < bH := mul_pos (inv_pos.mpr hΔpos) hℓ0pos
  have hdetH : 0 < aH * bH - cH ^ 2 := by
    have hform : aH * bH - cH ^ 2 = Δ⁻¹ := by
      unfold aH bH cH Δ
      field_simp [hΔne]
    rw [hform]
    exact inv_pos.mpr hΔpos
  have hInvExpr : G2⁻¹ = Δ⁻¹ • !![ℓ1, -c; -c, ℓ0] := by
    rw [Matrix.inv_def, hΔeq, Ring.inverse_eq_inv, hG2, adjugate_fin_two_of]
  have hH : G2⁻¹ = !![aH, cH; cH, bH] := by
    rw [hInvExpr]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [aH, Matrix.smul_apply, smul_eq_mul]
    · simp [cH, Matrix.smul_apply, smul_eq_mul]
    · simp [cH, Matrix.smul_apply, smul_eq_mul]
    · simp [bH, Matrix.smul_apply, smul_eq_mul]
  let e : Fin 2 ≃ Fin J.card := finCongr hcard.symm
  let y : Fin 2 → ℝ := fun i => x (e i)
  have hray := symm_fin_two_spd_rayleigh aH cH bH y haH hbH hdetH
  have htraceEq : (!![aH, cH; cH, bH]).trace = (G⁻¹).trace := by
    rw [← hH]
    exact selectedColGramCast_inv_trace A J hcard hGdet
  have hG2det : G2.det ≠ 0 := by
    rw [hG2det_eq]
    exact hGdet
  have hInvBack : (!![aH, cH; cH, bH])⁻¹ = G2 := by
    rw [← hH]
    exact nonsing_inv_nonsing_inv G2 (Ne.isUnit hG2det)
  have hreindex := quadForm_submatrix_finCongr G hcard x
  have hquad_energy : y ⬝ᵥ (G2 *ᵥ y) =
      vecEnergy (selectedCols A J *ᵥ x) := by
    have hform : y ⬝ᵥ (G2 *ᵥ y) = x ⬝ᵥ (G *ᵥ x) := by
      unfold y e G2 selectedColGramCast
      exact hreindex.symm
    rw [hform]
    exact (vecEnergy_selectedCols A J x).symm
  have hq : y ⬝ᵥ ((!![aH, cH; cH, bH])⁻¹ *ᵥ y) =
      vecEnergy (selectedCols A J *ᵥ x) := by
    rw [hInvBack, hquad_energy]
  have hv : vecEnergy x = vecEnergy y := by
    simpa [vecEnergy, y, e] using
      (Equiv.sum_comp e (fun j => x j ^ 2)).symm
  set B : ℝ := (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2))
  have hBge : (G⁻¹).trace ≤ B := by
    unfold G J B
    exact htr
  have hδ : 0 < (1 : ℝ) - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  have hBpos : 0 < B := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
    have hnum : 0 < (2 : ℝ) * τ ^ 2 * (n : ℝ) := by positivity
    exact div_pos hnum (mul_pos hkpos hδ)
  have hstep : vecEnergy x ≤
      (G⁻¹).trace * vecEnergy (selectedCols A J *ᵥ x) := by
    rw [hv, ← htraceEq, ← hq]
    exact hray
  have hle : vecEnergy x ≤ B * vecEnergy (selectedCols A J *ᵥ x) :=
    hstep.trans (mul_le_mul_of_nonneg_right hBge (vecEnergy_nonneg _))
  have hdiv : vecEnergy x / B ≤ vecEnergy (selectedCols A J *ᵥ x) := by
    rw [div_le_iff₀ hBpos, mul_comm]
    exact hle
  have hcoeff : ((k : ℝ) * (1 - ρ ^ 2)) / ((2 : ℝ) * τ ^ 2 * (n : ℝ)) * vecEnergy x =
      vecEnergy x / B := by
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hτne : τ ≠ 0 := (lt_of_lt_of_le zero_lt_one hτ).ne'
    have hδ0 : (1 : ℝ) - ρ ^ 2 ≠ 0 := hδ.ne'
    unfold B
    field_simp [hk0, hn0, hτne, hδ0]
  rw [hcoeff]
  exact hdiv

/-- Third CPQR pivot under the joint leverage-ratio and coherence
hypothesis. Does not bound pivots after the third. Does not close
outcome 3. Not a polynomial bound for every orthogonal-row matrix.
Not claimed sharp. -/
theorem joint_cpqr_three_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 3 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (selectedColGram A (cpqrIterate A 3)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A 3))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) +
          (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) *
            (((n : ℝ) - 2) / ((k : ℝ) - 2)) := by
  have hk2 : 2 ≤ k := by omega
  have hn3 : 3 ≤ n := by
    have hkn := orthogonalRows_le A hA
    omega
  let J := cpqrIterate A 2
  have hinv2 := cpqrIterate_invariant A hA 2 hk2
  have hcard : J.card = 2 := hinv2.1
  have hdet : (selectedColGram A J).det ≠ 0 := hinv2.2 (by omega)
  have hinv3 := cpqrIterate_invariant A hA 3 hk
  have hdet3 : (selectedColGram A (cpqrIterate A 3)).det ≠ 0 := hinv3.2 (by omega)
  have htr2 : ((selectedColGram A J)⁻¹).trace ≤
      (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
    obtain ⟨_, _, _, _, _, htr⟩ :=
      joint_cpqr_prefix_trace A hA hk2 hn τ ρ hτ hρ0 hρ hlev hcoh
    exact htr
  let μ : ℝ := ((k : ℝ) * (1 - ρ ^ 2)) / ((2 : ℝ) * τ ^ 2 * (n : ℝ))
  have hδ : 0 < 1 - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  have hμ : 0 < μ := by
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hτpos : 0 < τ := lt_of_lt_of_le zero_lt_one hτ
    exact div_pos (mul_pos hkpos hδ)
      (mul_pos (mul_pos (by norm_num) (pow_pos hτpos 2)) hnpos)
  let G := selectedColGram A J
  have hlower : ∀ x : Fin J.card → ℝ, μ * vecEnergy x ≤ x ⬝ᵥ (G *ᵥ x) := by
    intro x
    rw [← vecEnergy_selectedCols A J x]
    simpa [μ, G, J] using
      joint_cpqr_prefix_rayleigh A hA hk2 hn τ ρ hτ hρ0 hρ hlev hcoh x
  have hcardn : J.card < n := by
    rw [hcard]
    omega
  have hmax : ((k : ℝ) - 2) / ((n : ℝ) - 2) ≤ maxResidual A J := by
    have hcast : (J.card : ℝ) = 2 := by
      rw [hcard]
      norm_num
    have hrhs : ((k : ℝ) - (J.card : ℝ)) / ((n : ℝ) - (J.card : ℝ)) =
        ((k : ℝ) - 2) / ((n : ℝ) - 2) := by
      rw [hcast]
    simpa [hrhs] using nextResidual_ge A hA J hdet hcardn
  have havgpos : 0 < ((k : ℝ) - 2) / ((n : ℝ) - 2) := by
    refine div_pos ?_ ?_
    · have : (2 : ℝ) < (k : ℝ) := by exact_mod_cast (show 2 < k by omega)
      linarith
    · have : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (show 2 < n by omega)
      linarith
  have hmaxpos : 0 < maxResidual A J := lt_of_lt_of_le havgpos hmax
  have hunused : (unused J).Nonempty := by
    refine card_pos.mp ?_
    have : 0 < n - J.card := Nat.sub_pos_of_lt hcardn
    simpa [unused_card] using this
  obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_sup' hunused (residualSq A J)
  have hmaxeq : maxResidual A J = residualSq A J j0 := by
    unfold maxResidual
    rw [dif_pos hunused]
    exact hj0eq
  have hpos0 : 0 < residualSq A J j0 := by
    rw [← hmaxeq]
    exact hmaxpos
  let s := (unused J).filter fun j =>
    residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j
  have hs : s.Nonempty := by
    refine ⟨j0, mem_filter.mpr ⟨hj0, ?_, hpos0⟩⟩
    rw [hmaxeq]
  have hP : cpqrPivot A J = some (s.min' hs) := by
    unfold cpqrPivot
    simp only [s]
    rw [dif_pos hs]
  let j : Fin n := s.min' hs
  have hmem : j ∈ s := min'_mem _ hs
  have hresj : residualSq A J j = maxResidual A J := (mem_filter.mp hmem).2.1
  have hposj : 0 < residualSq A J j := (mem_filter.mp hmem).2.2
  have hj : j ∉ J := cpqrPivot_not_mem hP
  have hresge : ((k : ℝ) - 2) / ((n : ℝ) - 2) ≤ residualSq A J j := by
    rw [hresj]
    exact hmax
  let v : Fin k → ℝ := fun i => A i j
  let w : Fin J.card → ℝ := (selectedCols A J)ᵀ *ᵥ v
  let c : ℝ := (G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w)
  let q : ℝ := w ⬝ᵥ (G⁻¹ *ᵥ w)
  have hschur : residualSq A J j = v ⬝ᵥ v - q := by
    simpa [v, w, q, G] using residualSq_eq_schur A J j hdet
  have hℓ : v ⬝ᵥ v ≤ τ * (k : ℝ) / (n : ℝ) := by
    have hv : v ⬝ᵥ v = colInner A j j := rfl
    rw [hv, colInner_eq_residualSq]
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
    obtain ⟨jmin, _, hjmin⟩ :=
      exists_min_image (univ : Finset (Fin n)) (residualSq A ∅) hne
    have hsum := leverageSum A hA
    have hnmul : (n : ℝ) * residualSq A ∅ jmin ≤ (k : ℝ) := by
      have hle : ∑ t : Fin n, residualSq A ∅ jmin ≤ ∑ t : Fin n, residualSq A ∅ t :=
        sum_le_sum fun t ht => hjmin t ht
      rw [hsum] at hle
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      exact hle
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have havg : residualSq A ∅ jmin ≤ (k : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos, mul_comm]
      exact hnmul
    have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
    calc
      residualSq A ∅ j ≤ τ * residualSq A ∅ jmin := hlev j jmin
      _ ≤ τ * ((k : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left havg hτ0
      _ = τ * (k : ℝ) / (n : ℝ) := by rw [mul_div_assoc]
  have hcle : c ≤ (τ * (k : ℝ) / (n : ℝ)) / μ := by
    have hcq : c ≤ q / μ := by
      simpa [c, q, G] using inv_norm_sq_le_of_quad_lower G μ hμ hdet hlower w
    have hqle : q ≤ τ * (k : ℝ) / (n : ℝ) := by
      have hr0 : 0 ≤ residualSq A J j := residualSq_nonneg A J j
      rw [hschur] at hr0
      have hqv : q ≤ v ⬝ᵥ v := by linarith
      exact hqv.trans hℓ
    exact le_trans hcq (div_le_div_of_nonneg_right hqle hμ.le)
  have hclosed : (τ * (k : ℝ) / (n : ℝ)) / μ =
      (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2) := by
    unfold μ
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hτne : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hτ)
    have hδ0 : 1 - ρ ^ 2 ≠ 0 := ne_of_gt hδ
    field_simp [hn0, hk0, hτne, hδ0]
  have hnum : 1 + c ≤ 1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2) := by
    rw [← hclosed]
    linarith
  have hdenpos : 0 < residualSq A J j := hposj
  have hratio : (1 + c) / residualSq A J j ≤
      (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) /
        (((k : ℝ) - 2) / ((n : ℝ) - 2)) := by
    have hden : ((k : ℝ) - 2) / ((n : ℝ) - 2) ≤ residualSq A J j := hresge
    have hposnum : 0 ≤ 1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2) := by
      refine add_nonneg zero_le_one (div_nonneg ?_ hδ.le)
      exact mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans hτ) 3)
    exact le_trans
      (div_le_div_of_nonneg_right hnum hdenpos.le)
      (div_le_div_of_nonneg_left hposnum havgpos hden)
  have hratio' : (1 + c) / residualSq A J j ≤
      (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) *
        (((n : ℝ) - 2) / ((k : ℝ) - 2)) := by
    refine le_trans hratio ?_
    rw [div_eq_mul_inv, inv_div]
  have hsne :
      (fun i => A i j) ⬝ᵥ (fun i => A i j) -
        (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) ≠ 0 := by
    have h := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at h
    rw [h]
    exact ne_of_gt hposj
  have hinc :=
    append_inv_trace_increment (selectedCols A J) (fun i => A i j) hdet hsne
  have hfrac :
      (1 + ((((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) /
        ((fun i => A i j) ⬝ᵥ (fun i => A i j) -
          (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
              ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) =
        (1 + c) / residualSq A J j := by
    have hden := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at hden
    unfold c w G selectedColGram v
    rw [hden]
  have happdet :
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
    rw [appendColumn_gram_det_eq_insert A hj]
    have h3 : cpqrIterate A 3 = insert j J := by
      conv_lhs => unfold cpqrIterate
      rw [hP]
    rw [← h3]
    exact hdet3
  have hinsert := append_inv_trace_eq_insert A hj happdet
  refine ⟨hdet3, ?_⟩
  have h3 : cpqrIterate A 3 = insert j J := by
    conv_lhs => unfold cpqrIterate
    rw [hP]
  rw [h3, ← hinsert, hinc, hfrac]
  exact add_le_add htr2 hratio'

/-- For three rows, the joint leverage-ratio and coherence hypothesis bounds
the full CPQR set, not only a prefix. This is not a bound for general `k`.
It does not close outcome 3. It is not sharp. -/
theorem joint_cpqr_k3 {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : k = 3) (hn : 0 < n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (cpqrSet A).card = 3 ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
          (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
            ((2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
              (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2)) := by
  have hk3 : 3 ≤ k := by omega
  have hn3 : 3 ≤ n := by
    have hkn := orthogonalRows_le A hA
    omega
  have hn2 : 2 ≤ n := by omega
  have hpre := joint_cpqr_three_trace A hA hk3 hn2 τ ρ hτ hρ0 hρ hlev hcoh
  have hset : cpqrSet A = cpqrIterate A 3 := by
    simp [cpqrSet, hk]
  have hcard : (cpqrSet A).card = 3 := by
    rw [hset]
    exact (cpqrIterate_invariant A hA 3 hk3).1
  have hdet : (selectedColGram A (cpqrSet A)).det ≠ 0 := by
    rw [hset]
    exact hpre.1
  have hnum :
      (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) +
        (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) *
          (((n : ℝ) - 2) / ((k : ℝ) - 2)) =
        (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
          (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2) := by
    rw [hk]
    have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
    rw [hcast]
    have hone : ((3 : ℝ) - 2) = 1 := by norm_num
    rw [hone, div_one]
  have htr : ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
      (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
        (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2) := by
    rw [hset]
    exact hpre.2.trans (le_of_eq hnum)
  refine ⟨hcard, hdet, htr, ?_⟩
  intro x
  have henergy := selectedCols_energy_mul_inv_trace_ge A (cpqrSet A) hdet x
  exact henergy.trans (mul_le_mul_of_nonneg_left htr (vecEnergy_nonneg _))

/-- One CPQR pivot step under a leverage-ratio bound, assuming a trace
bound on the current prefix. Not a bound on the full `k`-set. Not a
polynomial bound. Does not close outcome 3. Coherence is not used. -/
theorem joint_cpqr_step {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (ht1 : 1 ≤ t) (htk : t < k) (htn : t < n) (τ B : ℝ)
    (hτ : 1 ≤ τ) (hB : 0 ≤ B)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (htr : ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B) :
    (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
        B + (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
          (((n : ℝ) - t) / ((k : ℝ) - t)) := by
  have htle : t ≤ k := le_of_lt htk
  have ht1le : t + 1 ≤ k := Nat.succ_le_of_lt htk
  let J := cpqrIterate A t
  have hinv := cpqrIterate_invariant A hA t htle
  have hcard : J.card = t := hinv.1
  have hdet : (selectedColGram A J).det ≠ 0 := hinv.2 (by omega)
  have hinv1 := cpqrIterate_invariant A hA (t + 1) ht1le
  have hdet1 : (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 :=
    hinv1.2 (Nat.succ_pos t)
  let G := selectedColGram A J
  let T : ℝ := (G⁻¹).trace
  have hTle : T ≤ B := by
    simpa [T, G, J] using htr
  have hTnn : 0 ≤ T := by
    simpa [T, G] using selectedColGram_inv_trace_nonneg A J hdet
  have hcardpos : 0 < J.card := by
    rw [hcard]
    omega
  let x0 : Fin J.card → ℝ := fun i => if i = ⟨0, hcardpos⟩ then 1 else 0
  have hx0 : vecEnergy x0 = 1 := by
    rw [vecEnergy, Finset.sum_eq_single (⟨0, hcardpos⟩ : Fin J.card)]
    · simp [x0]
    · intro i _ hi
      simp [x0, hi]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have hTpos : 0 < T := by
    have heng := selectedCols_energy_mul_inv_trace_ge A J hdet x0
    have hle : (1 : ℝ) ≤ vecEnergy (selectedCols A J *ᵥ x0) * T := by
      simpa [hx0, T, G] using heng
    by_contra hnot
    have hT0 : T = 0 := le_antisymm (le_of_not_gt hnot) hTnn
    rw [hT0, mul_zero] at hle
    linarith
  let μ : ℝ := 1 / T
  have hμ : 0 < μ := one_div_pos.mpr hTpos
  have hlower : ∀ x : Fin J.card → ℝ, μ * vecEnergy x ≤ x ⬝ᵥ (G *ᵥ x) := by
    intro x
    have heng := selectedCols_energy_mul_inv_trace_ge A J hdet x
    have hquad : vecEnergy (selectedCols A J *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
      simpa [G] using vecEnergy_selectedCols A J x
    have heng' : vecEnergy x ≤ (x ⬝ᵥ (G *ᵥ x)) * T := by
      simpa [hquad, T, G] using heng
    have hdiv : vecEnergy x / T ≤ x ⬝ᵥ (G *ᵥ x) :=
      (div_le_iff₀ hTpos).mpr heng'
    have hμeq : μ * vecEnergy x = vecEnergy x / T := by
      unfold μ
      rw [div_eq_mul_inv, one_mul, mul_comm, ← div_eq_mul_inv]
    exact hμeq.symm ▸ hdiv
  have hcardn : J.card < n := by
    rw [hcard]
    exact htn
  have hmax : ((k : ℝ) - t) / ((n : ℝ) - t) ≤ maxResidual A J := by
    have hcast : (J.card : ℝ) = (t : ℝ) := by exact_mod_cast hcard
    have hrhs : ((k : ℝ) - (J.card : ℝ)) / ((n : ℝ) - (J.card : ℝ)) =
        ((k : ℝ) - t) / ((n : ℝ) - t) := by
      rw [hcast]
    simpa [hrhs] using nextResidual_ge A hA J hdet hcardn
  have havgpos : 0 < ((k : ℝ) - t) / ((n : ℝ) - t) := by
    refine div_pos ?_ ?_
    · have : (t : ℝ) < (k : ℝ) := by exact_mod_cast htk
      linarith
    · have : (t : ℝ) < (n : ℝ) := by exact_mod_cast htn
      linarith
  have hmaxpos : 0 < maxResidual A J := lt_of_lt_of_le havgpos hmax
  have hunused : (unused J).Nonempty := by
    refine card_pos.mp ?_
    have : 0 < n - J.card := Nat.sub_pos_of_lt hcardn
    simpa [unused_card] using this
  obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_sup' hunused (residualSq A J)
  have hmaxeq : maxResidual A J = residualSq A J j0 := by
    unfold maxResidual
    rw [dif_pos hunused]
    exact hj0eq
  have hpos0 : 0 < residualSq A J j0 := by
    rw [← hmaxeq]
    exact hmaxpos
  let s := (unused J).filter fun j =>
    residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j
  have hs : s.Nonempty := by
    refine ⟨j0, mem_filter.mpr ⟨hj0, ?_, hpos0⟩⟩
    rw [hmaxeq]
  have hP : cpqrPivot A J = some (s.min' hs) := by
    unfold cpqrPivot
    simp only [s]
    rw [dif_pos hs]
  let j : Fin n := s.min' hs
  have hmem : j ∈ s := min'_mem _ hs
  have hresj : residualSq A J j = maxResidual A J := (mem_filter.mp hmem).2.1
  have hposj : 0 < residualSq A J j := (mem_filter.mp hmem).2.2
  have hj : j ∉ J := cpqrPivot_not_mem hP
  have hresge : ((k : ℝ) - t) / ((n : ℝ) - t) ≤ residualSq A J j := by
    rw [hresj]
    exact hmax
  let v : Fin k → ℝ := fun i => A i j
  let w : Fin J.card → ℝ := (selectedCols A J)ᵀ *ᵥ v
  let c : ℝ := (G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w)
  let q : ℝ := w ⬝ᵥ (G⁻¹ *ᵥ w)
  have hschur : residualSq A J j = v ⬝ᵥ v - q := by
    simpa [v, w, q, G] using residualSq_eq_schur A J j hdet
  have hℓ : v ⬝ᵥ v ≤ τ * (k : ℝ) / (n : ℝ) := by
    have hv : v ⬝ᵥ v = colInner A j j := rfl
    rw [hv, colInner_eq_residualSq]
    have hn0 : 0 < n := by omega
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, mem_univ _⟩
    obtain ⟨jmin, _, hjmin⟩ :=
      exists_min_image (univ : Finset (Fin n)) (residualSq A ∅) hne
    have hsum := leverageSum A hA
    have hnmul : (n : ℝ) * residualSq A ∅ jmin ≤ (k : ℝ) := by
      have hle : ∑ i : Fin n, residualSq A ∅ jmin ≤ ∑ i : Fin n, residualSq A ∅ i :=
        sum_le_sum fun i hi => hjmin i hi
      rw [hsum] at hle
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      exact hle
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have havg : residualSq A ∅ jmin ≤ (k : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos, mul_comm]
      exact hnmul
    have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
    calc
      residualSq A ∅ j ≤ τ * residualSq A ∅ jmin := hlev j jmin
      _ ≤ τ * ((k : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left havg hτ0
      _ = τ * (k : ℝ) / (n : ℝ) := by rw [mul_div_assoc]
  have hcnn : 0 ≤ c := by
    simpa [c, vecEnergy_eq_dot] using vecEnergy_nonneg (G⁻¹ *ᵥ w)
  have hcle : c ≤ (τ * (k : ℝ) / (n : ℝ)) * B := by
    have hcq : c ≤ q / μ := by
      simpa [c, q, G] using inv_norm_sq_le_of_quad_lower G μ hμ hdet hlower w
    have hqμ : q / μ = q * T := by
      unfold μ
      field_simp [hTpos.ne']
    have hqnn : 0 ≤ q := by
      have hprod : 0 ≤ q * T := by
        rw [← hqμ]
        exact le_trans hcnn hcq
      exact (mul_nonneg_iff_of_pos_right hTpos).mp hprod
    have hℓnn : 0 ≤ v ⬝ᵥ v := by
      simpa [vecEnergy_eq_dot] using vecEnergy_nonneg v
    have hqle : q ≤ v ⬝ᵥ v := by
      have hr0 : 0 ≤ residualSq A J j := residualSq_nonneg A J j
      rw [hschur] at hr0
      linarith
    have hqt : q * T ≤ (v ⬝ᵥ v) * B := by
      have h1 : q * T ≤ (v ⬝ᵥ v) * T := mul_le_mul_of_nonneg_right hqle hTnn
      have h2 : (v ⬝ᵥ v) * T ≤ (v ⬝ᵥ v) * B := mul_le_mul_of_nonneg_left hTle hℓnn
      exact h1.trans h2
    have hℓB : (v ⬝ᵥ v) * B ≤ (τ * (k : ℝ) / (n : ℝ)) * B :=
      mul_le_mul_of_nonneg_right hℓ hB
    have hcT : c ≤ q * T := by
      rw [← hqμ]
      exact hcq
    exact hcT.trans (hqt.trans hℓB)
  have hnum : 1 + c ≤ 1 + (τ * (k : ℝ) / (n : ℝ)) * B := by
    linarith
  have hdenpos : 0 < residualSq A J j := hposj
  have hratio : (1 + c) / residualSq A J j ≤
      (1 + (τ * (k : ℝ) / (n : ℝ)) * B) /
        (((k : ℝ) - t) / ((n : ℝ) - t)) := by
    have hden : ((k : ℝ) - t) / ((n : ℝ) - t) ≤ residualSq A J j := hresge
    have hposnum : 0 ≤ 1 + (τ * (k : ℝ) / (n : ℝ)) * B := by
      refine add_nonneg zero_le_one ?_
      refine mul_nonneg ?_ hB
      exact div_nonneg (mul_nonneg (zero_le_one.trans hτ) (by exact_mod_cast (Nat.zero_le k)))
        (by exact_mod_cast (Nat.zero_le n))
    exact le_trans
      (div_le_div_of_nonneg_right hnum hdenpos.le)
      (div_le_div_of_nonneg_left hposnum havgpos hden)
  have hratio' : (1 + c) / residualSq A J j ≤
      (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
        (((n : ℝ) - t) / ((k : ℝ) - t)) := by
    refine le_trans hratio ?_
    rw [div_eq_mul_inv, inv_div]
  have hsne :
      (fun i => A i j) ⬝ᵥ (fun i => A i j) -
        (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) ≠ 0 := by
    have h := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at h
    rw [h]
    exact ne_of_gt hposj
  have hinc :=
    append_inv_trace_increment (selectedCols A J) (fun i => A i j) hdet hsne
  have hfrac :
      (1 + ((((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) /
        ((fun i => A i j) ⬝ᵥ (fun i => A i j) -
          (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
              ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) =
        (1 + c) / residualSq A J j := by
    have hden := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at hden
    unfold c w G selectedColGram v
    rw [hden]
  have hnext : cpqrIterate A (t + 1) = insert j J := by
    conv_lhs => unfold cpqrIterate
    rw [hP]
  have happdet :
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
    rw [appendColumn_gram_det_eq_insert A hj]
    rw [← hnext]
    exact hdet1
  have hinsert := append_inv_trace_eq_insert A hj happdet
  refine ⟨hdet1, ?_⟩
  rw [hnext, ← hinsert, hinc, hfrac]
  exact add_le_add hTle hratio'

/-- Tighter than `milestoneE_joint_cpqr_step` by one copy of the current
trace. Still one step. Not an iteration. Not a polynomial bound. Does
not close outcome 3. -/
theorem joint_cpqr_step_tight {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (ht1 : 1 ≤ t) (htk : t < k) (htn : t < n) (τ B : ℝ)
    (hτ : 1 ≤ τ) (hB : 0 ≤ B)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (htr : ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B) :
    (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
        (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
          (((n : ℝ) - t) / ((k : ℝ) - t)) := by
  have htle : t ≤ k := le_of_lt htk
  have ht1le : t + 1 ≤ k := Nat.succ_le_of_lt htk
  let J := cpqrIterate A t
  have hinv := cpqrIterate_invariant A hA t htle
  have hcard : J.card = t := hinv.1
  have hdet : (selectedColGram A J).det ≠ 0 := hinv.2 (by omega)
  have hinv1 := cpqrIterate_invariant A hA (t + 1) ht1le
  have hdet1 : (selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 :=
    hinv1.2 (Nat.succ_pos t)
  let G := selectedColGram A J
  let T : ℝ := (G⁻¹).trace
  have hTle : T ≤ B := by
    simpa [T, G, J] using htr
  have hTnn : 0 ≤ T := by
    simpa [T, G] using selectedColGram_inv_trace_nonneg A J hdet
  have hcardpos : 0 < J.card := by
    rw [hcard]
    omega
  let x0 : Fin J.card → ℝ := fun i => if i = ⟨0, hcardpos⟩ then 1 else 0
  have hx0 : vecEnergy x0 = 1 := by
    rw [vecEnergy, Finset.sum_eq_single (⟨0, hcardpos⟩ : Fin J.card)]
    · simp [x0]
    · intro i _ hi
      simp [x0, hi]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  have hTpos : 0 < T := by
    have heng := selectedCols_energy_mul_inv_trace_ge A J hdet x0
    have hle : (1 : ℝ) ≤ vecEnergy (selectedCols A J *ᵥ x0) * T := by
      simpa [hx0, T, G] using heng
    by_contra hnot
    have hT0 : T = 0 := le_antisymm (le_of_not_gt hnot) hTnn
    rw [hT0, mul_zero] at hle
    linarith
  let μ : ℝ := 1 / T
  have hμ : 0 < μ := one_div_pos.mpr hTpos
  have hlower : ∀ x : Fin J.card → ℝ, μ * vecEnergy x ≤ x ⬝ᵥ (G *ᵥ x) := by
    intro x
    have heng := selectedCols_energy_mul_inv_trace_ge A J hdet x
    have hquad : vecEnergy (selectedCols A J *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
      simpa [G] using vecEnergy_selectedCols A J x
    have heng' : vecEnergy x ≤ (x ⬝ᵥ (G *ᵥ x)) * T := by
      simpa [hquad, T, G] using heng
    have hdiv : vecEnergy x / T ≤ x ⬝ᵥ (G *ᵥ x) :=
      (div_le_iff₀ hTpos).mpr heng'
    have hμeq : μ * vecEnergy x = vecEnergy x / T := by
      unfold μ
      rw [div_eq_mul_inv, one_mul, mul_comm, ← div_eq_mul_inv]
    exact hμeq.symm ▸ hdiv
  have hcardn : J.card < n := by
    rw [hcard]
    exact htn
  have hmax : ((k : ℝ) - t) / ((n : ℝ) - t) ≤ maxResidual A J := by
    have hcast : (J.card : ℝ) = (t : ℝ) := by exact_mod_cast hcard
    have hrhs : ((k : ℝ) - (J.card : ℝ)) / ((n : ℝ) - (J.card : ℝ)) =
        ((k : ℝ) - t) / ((n : ℝ) - t) := by
      rw [hcast]
    simpa [hrhs] using nextResidual_ge A hA J hdet hcardn
  have havgpos : 0 < ((k : ℝ) - t) / ((n : ℝ) - t) := by
    refine div_pos ?_ ?_
    · have : (t : ℝ) < (k : ℝ) := by exact_mod_cast htk
      linarith
    · have : (t : ℝ) < (n : ℝ) := by exact_mod_cast htn
      linarith
  have hmaxpos : 0 < maxResidual A J := lt_of_lt_of_le havgpos hmax
  have hunused : (unused J).Nonempty := by
    refine card_pos.mp ?_
    have : 0 < n - J.card := Nat.sub_pos_of_lt hcardn
    simpa [unused_card] using this
  obtain ⟨j0, hj0, hj0eq⟩ := Finset.exists_mem_eq_sup' hunused (residualSq A J)
  have hmaxeq : maxResidual A J = residualSq A J j0 := by
    unfold maxResidual
    rw [dif_pos hunused]
    exact hj0eq
  have hpos0 : 0 < residualSq A J j0 := by
    rw [← hmaxeq]
    exact hmaxpos
  let s := (unused J).filter fun j =>
    residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j
  have hs : s.Nonempty := by
    refine ⟨j0, mem_filter.mpr ⟨hj0, ?_, hpos0⟩⟩
    rw [hmaxeq]
  have hP : cpqrPivot A J = some (s.min' hs) := by
    unfold cpqrPivot
    simp only [s]
    rw [dif_pos hs]
  let j : Fin n := s.min' hs
  have hmem : j ∈ s := min'_mem _ hs
  have hresj : residualSq A J j = maxResidual A J := (mem_filter.mp hmem).2.1
  have hposj : 0 < residualSq A J j := (mem_filter.mp hmem).2.2
  have hj : j ∉ J := cpqrPivot_not_mem hP
  have hresge : ((k : ℝ) - t) / ((n : ℝ) - t) ≤ residualSq A J j := by
    rw [hresj]
    exact hmax
  let v : Fin k → ℝ := fun i => A i j
  let w : Fin J.card → ℝ := (selectedCols A J)ᵀ *ᵥ v
  let c : ℝ := (G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w)
  let q : ℝ := w ⬝ᵥ (G⁻¹ *ᵥ w)
  have hschur : residualSq A J j = v ⬝ᵥ v - q := by
    simpa [v, w, q, G] using residualSq_eq_schur A J j hdet
  have hℓ : v ⬝ᵥ v ≤ τ * (k : ℝ) / (n : ℝ) := by
    have hv : v ⬝ᵥ v = colInner A j j := rfl
    rw [hv, colInner_eq_residualSq]
    have hn0 : 0 < n := by omega
    have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn0⟩, mem_univ _⟩
    obtain ⟨jmin, _, hjmin⟩ :=
      exists_min_image (univ : Finset (Fin n)) (residualSq A ∅) hne
    have hsum := leverageSum A hA
    have hnmul : (n : ℝ) * residualSq A ∅ jmin ≤ (k : ℝ) := by
      have hle : ∑ i : Fin n, residualSq A ∅ jmin ≤ ∑ i : Fin n, residualSq A ∅ i :=
        sum_le_sum fun i hi => hjmin i hi
      rw [hsum] at hle
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      exact hle
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have havg : residualSq A ∅ jmin ≤ (k : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos, mul_comm]
      exact hnmul
    have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
    calc
      residualSq A ∅ j ≤ τ * residualSq A ∅ jmin := hlev j jmin
      _ ≤ τ * ((k : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left havg hτ0
      _ = τ * (k : ℝ) / (n : ℝ) := by rw [mul_div_assoc]
  have hcq : c ≤ q / μ := by
    simpa [c, q, G] using inv_norm_sq_le_of_quad_lower G μ hμ hdet hlower w
  have hqμ : q / μ = q * T := by
    unfold μ
    field_simp [hTpos.ne']
  have hcT : c ≤ q * T := by
    rw [← hqμ]
    exact hcq
  have hqeq : q = v ⬝ᵥ v - residualSq A J j := by
    have hsum : residualSq A J j + q = v ⬝ᵥ v := (eq_sub_iff_add_eq).mp hschur
    have hcomm : q + residualSq A J j = v ⬝ᵥ v := by
      rwa [add_comm] at hsum
    exact (eq_sub_iff_add_eq).mpr hcomm
  have hcsub : c ≤ T * (v ⬝ᵥ v - residualSq A J j) := by
    calc
      c ≤ q * T := hcT
      _ = T * q := by rw [mul_comm]
      _ = T * (v ⬝ᵥ v - residualSq A J j) := by rw [hqeq]
  have h1c : 1 + c ≤ 1 + T * (v ⬝ᵥ v) - T * residualSq A J j := by
    calc
      1 + c = c + 1 := by rw [add_comm]
      _ ≤ T * (v ⬝ᵥ v - residualSq A J j) + 1 := add_le_add_left hcsub 1
      _ = 1 + T * (v ⬝ᵥ v - residualSq A J j) := by rw [add_comm]
      _ = 1 + (T * (v ⬝ᵥ v) - T * residualSq A J j) := by rw [mul_sub]
      _ = 1 + T * (v ⬝ᵥ v) - T * residualSq A J j := by rw [← add_sub_assoc]
  have hdiv : (1 + c) / residualSq A J j ≤
      (1 + T * (v ⬝ᵥ v)) / residualSq A J j - T := by
    have hquot : (1 + c) / residualSq A J j ≤
        (1 + T * (v ⬝ᵥ v) - T * residualSq A J j) / residualSq A J j :=
      div_le_div_of_nonneg_right h1c hposj.le
    have hsplit :
        (1 + T * (v ⬝ᵥ v) - T * residualSq A J j) / residualSq A J j =
          (1 + T * (v ⬝ᵥ v)) / residualSq A J j - T := by
      rw [sub_div, mul_div_cancel_right₀ _ hposj.ne']
    exact hquot.trans (le_of_eq hsplit)
  have hTcancel :
      T + ((1 + T * (v ⬝ᵥ v)) / residualSq A J j - T) =
        (1 + T * (v ⬝ᵥ v)) / residualSq A J j := by
    set x : ℝ := (1 + T * (v ⬝ᵥ v)) / residualSq A J j
    calc
      T + (x - T) = x - T + T := by rw [add_comm]
      _ = x := sub_add_cancel _ _
  have hℓnn : 0 ≤ v ⬝ᵥ v := by
    simpa [vecEnergy_eq_dot] using vecEnergy_nonneg v
  have hposnum : 0 ≤ 1 + T * (v ⬝ᵥ v) :=
    add_nonneg zero_le_one (mul_nonneg hTnn hℓnn)
  have hprod : T * (v ⬝ᵥ v) ≤ (τ * (k : ℝ) / (n : ℝ)) * B := by
    calc
      T * (v ⬝ᵥ v) ≤ B * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right hTle hℓnn
      _ ≤ B * (τ * (k : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left hℓ hB
      _ = (τ * (k : ℝ) / (n : ℝ)) * B := by rw [mul_comm]
  have hcoeff : 1 + T * (v ⬝ᵥ v) ≤ 1 + (τ * (k : ℝ) / (n : ℝ)) * B := by
    linarith
  have hrest : (1 + T * (v ⬝ᵥ v)) / residualSq A J j ≤
      (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
        (((n : ℝ) - t) / ((k : ℝ) - t)) := by
    have hcompare : (1 + T * (v ⬝ᵥ v)) / residualSq A J j ≤
        (1 + T * (v ⬝ᵥ v)) / (((k : ℝ) - t) / ((n : ℝ) - t)) :=
      div_le_div_of_nonneg_left hposnum havgpos hresge
    have hdivB : (1 + T * (v ⬝ᵥ v)) / (((k : ℝ) - t) / ((n : ℝ) - t)) ≤
        (1 + (τ * (k : ℝ) / (n : ℝ)) * B) /
          (((k : ℝ) - t) / ((n : ℝ) - t)) :=
      div_le_div_of_nonneg_right hcoeff havgpos.le
    have hflip : (1 + (τ * (k : ℝ) / (n : ℝ)) * B) /
          (((k : ℝ) - t) / ((n : ℝ) - t)) =
        (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
          (((n : ℝ) - t) / ((k : ℝ) - t)) := by
      rw [div_eq_mul_inv, inv_div]
    exact hcompare.trans (hdivB.trans (le_of_eq hflip))
  have hsne :
      (fun i => A i j) ⬝ᵥ (fun i => A i j) -
        (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j))) ≠ 0 := by
    have h := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at h
    rw [h]
    exact ne_of_gt hposj
  have hinc :=
    append_inv_trace_increment (selectedCols A J) (fun i => A i j) hdet hsne
  have hfrac :
      (1 + ((((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)) ⬝ᵥ
          (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
            ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) /
        ((fun i => A i j) ⬝ᵥ (fun i => A i j) -
          (((selectedCols A J)ᵀ *ᵥ fun i => A i j) ⬝ᵥ
            (((selectedCols A J)ᵀ * selectedCols A J)⁻¹ *ᵥ
              ((selectedCols A J)ᵀ *ᵥ fun i => A i j)))) =
        (1 + c) / residualSq A J j := by
    have hden := (residualSq_eq_schur A J j hdet).symm
    unfold selectedColGram at hden
    unfold c w G selectedColGram v
    rw [hden]
  have hnext : cpqrIterate A (t + 1) = insert j J := by
    conv_lhs => unfold cpqrIterate
    rw [hP]
  have happdet :
      ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
          appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
    rw [appendColumn_gram_det_eq_insert A hj]
    rw [← hnext]
    exact hdet1
  have hinsert := append_inv_trace_eq_insert A hj happdet
  refine ⟨hdet1, ?_⟩
  rw [hnext, ← hinsert, hinc, hfrac]
  refine (add_le_add (le_refl T) hdiv).trans ?_
  rw [hTcancel]
  exact hrest

/-- Iterated CPQR inverse-trace majorant. The value at `2` is the length-2
prefix bound. For `s ≥ 2`, the value at `s + 1` is the one-step increment
from `joint_cpqr_step`. Each step multiplies the previous bound by
`1 + (τ k / n) (n - s) / (k - s)` and adds `(n - s) / (k - s)`. That factor
is `O(τ k)` near the last pivot. This is not a polynomial in `k`. -/
noncomputable def jointTraceBound (k n : ℕ) (τ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2))
  | s + 1 =>
      let B := jointTraceBound k n τ ρ s
      B + (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
        (((n : ℝ) - s) / ((k : ℝ) - s))

lemma jointTraceBound_two (k n : ℕ) (τ ρ : ℝ) :
    jointTraceBound k n τ ρ 2 =
      (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
  rfl

lemma jointTraceBound_succ {k n : ℕ} {τ ρ : ℝ} {s : ℕ} (hs : 2 ≤ s) :
    jointTraceBound k n τ ρ (s + 1) =
      jointTraceBound k n τ ρ s +
        (1 + (τ * (k : ℝ) / (n : ℝ)) * jointTraceBound k n τ ρ s) *
          (((n : ℝ) - s) / ((k : ℝ) - s)) := by
  match s, hs with
  | 0, hs => omega
  | 1, hs => omega
  | _ + 2, _ => rfl

lemma jointTraceBound_two_nonneg {k n : ℕ} {τ ρ : ℝ}
    (hk : 2 ≤ k) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    0 ≤ (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 0 ≤ n by omega)
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hsq : ρ ^ 2 < 1 := by
    have hle : ρ ^ 2 ≤ ρ := by
      calc
        ρ ^ 2 = ρ * ρ := by rw [pow_two]
        _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (le_of_lt hρ) hρ0
        _ = ρ := mul_one ρ
    exact lt_of_le_of_lt hle hρ
  have hden : 0 < (k : ℝ) * (1 - ρ ^ 2) := mul_pos hk0 (by linarith)
  have hnum : 0 ≤ (2 : ℝ) * τ ^ 2 * (n : ℝ) := by
    have hτsq : 0 ≤ τ ^ 2 := sq_nonneg τ
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    exact mul_nonneg (mul_nonneg h2 hτsq) hn0
  exact div_nonneg hnum hden.le

lemma jointTraceBound_step_nonneg {k n : ℕ} {τ B : ℝ} {s : ℕ}
    (hτ : 1 ≤ τ) (hB : 0 ≤ B) (hsk : s < k) (hsn : s < n) :
    0 ≤ B + (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
      (((n : ℝ) - s) / ((k : ℝ) - s)) := by
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcoeff : 0 ≤ τ * (k : ℝ) / (n : ℝ) :=
    div_nonneg (mul_nonneg hτ0 (Nat.cast_nonneg k)) (le_of_lt hn0)
  have hfactor : 0 ≤ 1 + (τ * (k : ℝ) / (n : ℝ)) * B :=
    add_nonneg zero_le_one (mul_nonneg hcoeff hB)
  have hnum : 0 ≤ (n : ℝ) - s :=
    sub_nonneg.mpr (by exact_mod_cast (le_of_lt hsn))
  have hden : 0 ≤ (k : ℝ) - s :=
    sub_nonneg.mpr (by exact_mod_cast (le_of_lt hsk))
  exact add_nonneg hB (mul_nonneg hfactor (div_nonneg hnum hden))

lemma jointTraceBound_nonneg {k n : ℕ} {τ ρ : ℝ}
    (hk : 2 ≤ k) (hn : 2 ≤ n) (hkn : k ≤ n)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ∀ s, 2 ≤ s → s ≤ k → 0 ≤ jointTraceBound k n τ ρ s := by
  intro s hs2 hsk
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases htwo : s + 1 = 2
    · rw [htwo, jointTraceBound_two]
      exact jointTraceBound_two_nonneg hk hn hτ hρ0 hρ
    · have hs2' : 2 ≤ s := by omega
      have hsltk : s < k := by omega
      have hslek : s ≤ k := le_of_lt hsltk
      have hsn : s < n := lt_of_lt_of_le hsltk hkn
      rw [jointTraceBound_succ hs2']
      exact jointTraceBound_step_nonneg hτ (ih hs2' hslek) hsltk hsn

/-- Tight iteration of the CPQR inverse-trace step. The value at `2` is
the length-2 prefix bound. For `s ≥ 2`, the value at `s + 1` is
`(1 + (τ k / n) B) (n - s) / (k - s)` with no added copy of `B`.
When `n = k`, this sends `B` to `1 + τ B`, so `τ > 1` is still
exponential in the number of pivots. When `n > k`, the factor
`(n - s) / (k - s)` is not a polynomial bound. This is not a polynomial
in `k`. -/
noncomputable def jointTraceBoundTight (k n : ℕ) (τ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2))
  | s + 1 =>
      let B := jointTraceBoundTight k n τ ρ s
      (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
        (((n : ℝ) - s) / ((k : ℝ) - s))

lemma jointTraceBoundTight_two (k n : ℕ) (τ ρ : ℝ) :
    jointTraceBoundTight k n τ ρ 2 =
      (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := by
  rfl

lemma jointTraceBoundTight_succ {k n : ℕ} {τ ρ : ℝ} {s : ℕ} (hs : 2 ≤ s) :
    jointTraceBoundTight k n τ ρ (s + 1) =
      (1 + (τ * (k : ℝ) / (n : ℝ)) * jointTraceBoundTight k n τ ρ s) *
        (((n : ℝ) - s) / ((k : ℝ) - s)) := by
  match s, hs with
  | 0, hs => omega
  | 1, hs => omega
  | _ + 2, _ => rfl

lemma jointTraceBoundTight_step_nonneg {k n : ℕ} {τ B : ℝ} {s : ℕ}
    (hτ : 1 ≤ τ) (hB : 0 ≤ B) (hsk : s < k) (hsn : s < n) :
    0 ≤ (1 + (τ * (k : ℝ) / (n : ℝ)) * B) *
      (((n : ℝ) - s) / ((k : ℝ) - s)) := by
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcoeff : 0 ≤ τ * (k : ℝ) / (n : ℝ) :=
    div_nonneg (mul_nonneg hτ0 (Nat.cast_nonneg k)) (le_of_lt hn0)
  have hfactor : 0 ≤ 1 + (τ * (k : ℝ) / (n : ℝ)) * B :=
    add_nonneg zero_le_one (mul_nonneg hcoeff hB)
  have hnum : 0 ≤ (n : ℝ) - s :=
    sub_nonneg.mpr (by exact_mod_cast (le_of_lt hsn))
  have hden : 0 ≤ (k : ℝ) - s :=
    sub_nonneg.mpr (by exact_mod_cast (le_of_lt hsk))
  exact mul_nonneg hfactor (div_nonneg hnum hden)

lemma jointTraceBoundTight_nonneg {k n : ℕ} {τ ρ : ℝ}
    (hk : 2 ≤ k) (hn : 2 ≤ n) (hkn : k ≤ n)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    ∀ s, 2 ≤ s → s ≤ k → 0 ≤ jointTraceBoundTight k n τ ρ s := by
  intro s hs2 hsk
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases htwo : s + 1 = 2
    · rw [htwo, jointTraceBoundTight_two]
      exact jointTraceBound_two_nonneg hk hn hτ hρ0 hρ
    · have hs2' : 2 ≤ s := by omega
      have hsltk : s < k := by omega
      have hslek : s ≤ k := le_of_lt hsltk
      have hsn : s < n := lt_of_lt_of_le hsltk hkn
      rw [jointTraceBoundTight_succ hs2']
      exact jointTraceBoundTight_step_nonneg hτ (ih hs2' hslek) hsltk hsn

/-- For every prefix length `2 ≤ t ≤ k`, the CPQR Gram inverse trace is at
most `jointTraceBound`. The same bound controls the Rayleigh comparison.
This is not a polynomial in `k`. It does not close outcome 3. It is not a
bound for matrices outside the leverage-ratio and coherence hypotheses. -/
theorem joint_cpqr_trace_bound {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (ht2 : 2 ≤ t) (htk : t ≤ k) :
    (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
        jointTraceBound k n τ ρ t ∧
      ∀ x : Fin (cpqrIterate A t).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) *
            jointTraceBound k n τ ρ t := by
  have hkn : k ≤ n := orthogonalRows_le A hA
  suffices
      ∀ t, 2 ≤ t → t ≤ k →
        (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
          ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
            jointTraceBound k n τ ρ t ∧
          ∀ x : Fin (cpqrIterate A t).card → ℝ,
            vecEnergy x ≤
              vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) *
                jointTraceBound k n τ ρ t from this t ht2 htk
  intro t ht2 htk
  induction t with
  | zero => omega
  | succ s ih =>
    by_cases htwo : s + 1 = 2
    · rw [htwo]
      obtain ⟨_, _, _, _, hdet, htr⟩ :=
        joint_cpqr_prefix_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh
      have htrb :
          ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
            jointTraceBound k n τ ρ 2 := by
        rw [jointTraceBound_two]
        exact htr
      refine ⟨hdet, htrb, ?_⟩
      intro x
      have henergy :=
        selectedCols_energy_mul_inv_trace_ge A (cpqrIterate A 2) hdet x
      exact henergy.trans (mul_le_mul_of_nonneg_left htrb (vecEnergy_nonneg _))
    · have hs2 : 2 ≤ s := by omega
      have hsltk : s < k := by omega
      have hslek : s ≤ k := le_of_lt hsltk
      have hsn : s < n := lt_of_lt_of_le hsltk hkn
      have hs1 : 1 ≤ s := by omega
      have ihP := ih hs2 hslek
      have hBnn : 0 ≤ jointTraceBound k n τ ρ s :=
        jointTraceBound_nonneg hk hn hkn hτ hρ0 hρ s hs2 hslek
      have hstep :=
        joint_cpqr_step A hA hs1 hsltk hsn τ (jointTraceBound k n τ ρ s)
          hτ hBnn hlev ihP.2.1
      have htrb :
          ((selectedColGram A (cpqrIterate A (s + 1)))⁻¹).trace ≤
            jointTraceBound k n τ ρ (s + 1) := by
        rw [jointTraceBound_succ hs2]
        exact hstep.2
      refine ⟨hstep.1, htrb, ?_⟩
      intro x
      have henergy :=
        selectedCols_energy_mul_inv_trace_ge A (cpqrIterate A (s + 1)) hstep.1 x
      exact henergy.trans (mul_le_mul_of_nonneg_left htrb (vecEnergy_nonneg _))

/-- Iterates `joint_cpqr_step_tight`, not the loose step. Not a polynomial
in `k`. Does not close outcome 3. Not a bound outside the leverage-ratio
and coherence hypotheses. Coherence is used only at length 2. The loose
recurrence `jointTraceBound` is unchanged. On the identity at `τ = 1`,
`ρ = 0`, `n = k`, the tight values are `2, 3, 4, ...` while the loose
values are `2, 5, 11, ...`. Equality of trace and bound is asserted only
for those identity checks, not in general. -/
theorem joint_cpqr_trace_bound_tight {k n t : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (hn : 2 ≤ n) (τ ρ : ℝ)
    (hτ : 1 ≤ τ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin n, residualSq A ∅ i ≤ τ * residualSq A ∅ j)
    (hcoh : ∀ i j : Fin n, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (ht2 : 2 ≤ t) (htk : t ≤ k) :
    (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
      ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
        jointTraceBoundTight k n τ ρ t ∧
      ∀ x : Fin (cpqrIterate A t).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) *
            jointTraceBoundTight k n τ ρ t := by
  have hkn : k ≤ n := orthogonalRows_le A hA
  suffices
      ∀ t, 2 ≤ t → t ≤ k →
        (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
          ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
            jointTraceBoundTight k n τ ρ t ∧
          ∀ x : Fin (cpqrIterate A t).card → ℝ,
            vecEnergy x ≤
              vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) *
                jointTraceBoundTight k n τ ρ t from this t ht2 htk
  intro t ht2 htk
  induction t with
  | zero => omega
  | succ s ih =>
    by_cases htwo : s + 1 = 2
    · rw [htwo]
      obtain ⟨_, _, _, _, hdet, htr⟩ :=
        joint_cpqr_prefix_trace A hA hk hn τ ρ hτ hρ0 hρ hlev hcoh
      have htrb :
          ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
            jointTraceBoundTight k n τ ρ 2 := by
        rw [jointTraceBoundTight_two]
        exact htr
      refine ⟨hdet, htrb, ?_⟩
      intro x
      have henergy :=
        selectedCols_energy_mul_inv_trace_ge A (cpqrIterate A 2) hdet x
      exact henergy.trans (mul_le_mul_of_nonneg_left htrb (vecEnergy_nonneg _))
    · have hs2 : 2 ≤ s := by omega
      have hsltk : s < k := by omega
      have hslek : s ≤ k := le_of_lt hsltk
      have hsn : s < n := lt_of_lt_of_le hsltk hkn
      have hs1 : 1 ≤ s := by omega
      have ihP := ih hs2 hslek
      have hBnn : 0 ≤ jointTraceBoundTight k n τ ρ s :=
        jointTraceBoundTight_nonneg hk hn hkn hτ hρ0 hρ s hs2 hslek
      have hstep :=
        joint_cpqr_step_tight A hA hs1 hsltk hsn τ
          (jointTraceBoundTight k n τ ρ s) hτ hBnn hlev ihP.2.1
      have htrb :
          ((selectedColGram A (cpqrIterate A (s + 1)))⁻¹).trace ≤
            jointTraceBoundTight k n τ ρ (s + 1) := by
        rw [jointTraceBoundTight_succ hs2]
        exact hstep.2
      refine ⟨hstep.1, htrb, ?_⟩
      intro x
      have henergy :=
        selectedCols_energy_mul_inv_trace_ge A
          (cpqrIterate A (s + 1)) hstep.1 x
      exact henergy.trans (mul_le_mul_of_nonneg_left htrb (vecEnergy_nonneg _))

/-- Prefix inverse-trace bound for square equal-leverage CPQR. Not a
public theorem. Square equal-leverage only. Not a polynomial bound for
rectangular or `τ > 1` matrices. Does not close outcome 3. -/
lemma joint_square_equal_prefix {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin k, residualSq A ∅ i ≤ residualSq A ∅ j)
    (hcoh : ∀ i j : Fin k, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j))
    (t : ℕ) (ht2 : 2 ≤ t) :
    t ≤ k →
      (selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
        ((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤
          (t : ℝ) - 2 + 2 / (1 - ρ ^ 2) := by
  have hlev1 : ∀ i j : Fin k, residualSq A ∅ i ≤ (1 : ℝ) * residualSq A ∅ j := by
    intro i j
    simpa [one_mul] using hlev i j
  have hδ : 0 < (1 : ℝ) - ρ ^ 2 := by
    have : ρ ^ 2 < 1 := (sq_lt_one_iff₀ hρ0).2 hρ
    linarith
  induction t, ht2 using Nat.le_induction with
  | base =>
    intro _
    obtain ⟨_, _, _, _, hdet, htr⟩ :=
      joint_cpqr_prefix_trace A hA hk hk (1 : ℝ) ρ le_rfl hρ0 hρ hlev1 hcoh
    have hprefix_eq :
        (2 : ℝ) * (1 : ℝ) ^ 2 * (k : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) =
          (2 : ℝ) / (1 - ρ ^ 2) := by
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have hδ0 : (1 : ℝ) - ρ ^ 2 ≠ 0 := ne_of_gt hδ
      field_simp [hk0, hδ0]
    have htwo_eq :
        (2 : ℝ) - 2 + 2 / (1 - ρ ^ 2) = (2 : ℝ) / (1 - ρ ^ 2) := by
      have : (2 : ℝ) - 2 = 0 := by norm_num
      rw [this, zero_add]
    refine ⟨hdet, ?_⟩
    calc
      ((selectedColGram A (cpqrIterate A 2))⁻¹).trace
          ≤ (2 : ℝ) * (1 : ℝ) ^ 2 * (k : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) := htr
      _ = (2 : ℝ) / (1 - ρ ^ 2) := hprefix_eq
      _ = (2 : ℝ) - 2 + 2 / (1 - ρ ^ 2) := htwo_eq.symm
  | succ m hm ih =>
    intro hmk
    have ihP := ih (Nat.le_of_succ_le hmk)
    have hmlt : m < k := Nat.lt_of_succ_le hmk
    have hm1 : 1 ≤ m := le_trans one_le_two hm
    let B : ℝ := (m : ℝ) - 2 + 2 / (1 - ρ ^ 2)
    have hBnn : 0 ≤ B := by
      have hsub : 0 ≤ (m : ℝ) - 2 := sub_nonneg.mpr (by exact_mod_cast hm)
      have hpos : 0 ≤ (2 : ℝ) / (1 - ρ ^ 2) :=
        le_of_lt (div_pos (by norm_num) hδ)
      exact add_nonneg hsub hpos
    have htrB : ((selectedColGram A (cpqrIterate A m))⁻¹).trace ≤ B := ihP.2
    have hstep :=
      joint_cpqr_step_tight A hA hm1 hmlt hmlt (1 : ℝ) B le_rfl hBnn hlev1 htrB
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hcoeff : (1 : ℝ) * (k : ℝ) / (k : ℝ) = 1 :=
      mul_div_cancel_right₀ (1 : ℝ) hk0
    have hquot : ((k : ℝ) - (m : ℝ)) / ((k : ℝ) - (m : ℝ)) = 1 := by
      have hmkl : (m : ℝ) < (k : ℝ) := by exact_mod_cast hmlt
      exact div_self (sub_ne_zero.mpr (ne_of_gt hmkl))
    have hstep_eq :
        (1 + ((1 : ℝ) * (k : ℝ) / (k : ℝ)) * B) *
            (((k : ℝ) - (m : ℝ)) / ((k : ℝ) - (m : ℝ))) =
          (1 : ℝ) + B := by
      rw [hcoeff, hquot, one_mul, mul_one]
    have hnext :
        (1 : ℝ) + B = ((m + 1 : ℕ) : ℝ) - 2 + 2 / (1 - ρ ^ 2) := by
      unfold B
      rw [Nat.cast_succ]
      abel
    have htr := hstep.2
    rw [hstep_eq, hnext] at htr
    exact ⟨hstep.1, htr⟩

/-- Square equal-leverage only. Not a polynomial bound for rectangular or
`τ > 1` matrices. Does not close outcome 3. Not claimed sharp for `ρ > 0`.
On the identity at `ρ = 0` the bound equals `k`, and the inverse trace
equals `k`. -/
theorem joint_square_equal_trace {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : OrthogonalRows A)
    (hk : 2 ≤ k) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hlev : ∀ i j : Fin k, residualSq A ∅ i ≤ residualSq A ∅ j)
    (hcoh : ∀ i j : Fin k, i ≠ j →
      |colInner A i j| ≤
        ρ * Real.sqrt (residualSq A ∅ i) * Real.sqrt (residualSq A ∅ j)) :
    (cpqrSet A).card = k ∧
      (selectedColGram A (cpqrSet A)).det ≠ 0 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) - 2 + 2 / (1 - ρ ^ 2) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy x ≤
          vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
            ((k : ℝ) - 2 + 2 / (1 - ρ ^ 2)) := by
  have hpre :=
    joint_square_equal_prefix A hA hk ρ hρ0 hρ hlev hcoh k hk le_rfl
  have hcard : (cpqrSet A).card = k := cpqrSet_card_eq A hA
  have hset : cpqrSet A = cpqrIterate A k := rfl
  have hdet : (selectedColGram A (cpqrSet A)).det ≠ 0 := by
    rw [hset]
    exact hpre.1
  have htr :
      ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) - 2 + 2 / (1 - ρ ^ 2) := by
    rw [hset]
    exact hpre.2
  refine ⟨hcard, hdet, htr, ?_⟩
  intro x
  have henergy :=
    selectedCols_energy_mul_inv_trace_ge A (cpqrSet A) hdet x
  exact henergy.trans (mul_le_mul_of_nonneg_left htr (vecEnergy_nonneg _))

end StructuredColumnSelection
