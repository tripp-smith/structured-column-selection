import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.VolumeWeights
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Inverse-norm expectation and finite Markov bound

Milestone D wraps the adjugate identity of Milestone C as a finite
volume-weighted expectation of inverse-Frobenius energy, then applies
a purely finitary Markov inequality.

On an invertible block, `tr(adj(A_J A_Jᵀ)) = det(A_J)² ‖A_J⁻¹‖_F²`.
The same trace is used for every `k`-set, so singular summands stay
defined. The resulting tail bound controls the Frobenius quantity and
therefore also the spectral norm on the invertible locus.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

variable {R : Type*} [CommRing R]

/-- Volume-weighted inverse-Frobenius energy `tr(adj(A_J A_Jᵀ))`. -/
def invFrobWeight {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : R :=
  (volumeWeightedInvGram A J).trace

lemma volumeWeight_nonneg {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) : 0 ≤ volumeWeight A J := by
  unfold volumeWeight
  split_ifs
  · exact sq_nonneg _
  · rfl

lemma det_mul_transpose_nonneg {k n : ℕ} (B : Matrix (Fin k) (Fin n) ℝ) :
    0 ≤ (B * (Bᵀ)).det := by
  rw [← volumeWeights_sum_eq_det_mul_transpose]
  exact sum_nonneg fun _ _ => volumeWeight_nonneg _ _

lemma invFrobWeight_eq_zero_of_card {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) {J : Finset (Fin n)} (hJ : J.card ≠ k) :
    invFrobWeight A J = 0 := by
  simp [invFrobWeight, volumeWeightedInvGram, hJ, Matrix.trace_zero]

lemma invFrobWeight_nonneg {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) : 0 ≤ invFrobWeight A J := by
  unfold invFrobWeight volumeWeightedInvGram
  split_ifs with h
  · cases k with
    | zero =>
      simp [Matrix.adjugate_fin_zero, Matrix.trace_eq_zero_of_isEmpty]
    | succ m =>
      rw [Matrix.trace]
      refine sum_nonneg fun i _ => ?_
      change 0 ≤ Matrix.adjugate
          (colsSubmatrix A J h * ((colsSubmatrix A J h)ᵀ)) i i
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      have hsgn : (-1 : ℝ) ^ (i + i : ℕ) = 1 := by
        rw [← two_mul, pow_mul, neg_one_pow_two, one_pow]
      rw [hsgn, one_mul, submatrix_mul_transpose]
      exact det_mul_transpose_nonneg _
  · simp [Matrix.trace_zero]

/-- Finite inverse-Frobenius expectation, without orthogonality. -/
theorem invFrobWeights_sum {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, invFrobWeight A J =
      ((n + 1 - k : ℕ) : R) * (Matrix.adjugate (A * (Aᵀ))).trace := by
  simp [invFrobWeight, ← Matrix.trace_sum, volumeWeightedInvGrams_sum,
    Matrix.trace_smul, nsmul_eq_mul, mul_comm]

/-- Milestone D: volume-weighted inverse-Frobenius energy equals
`k(n-k+1)` when `A Aᵀ = I`. -/
theorem expectedInvFrobSq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, invFrobWeight A J =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) := by
  rw [← Matrix.trace_sum]
  change (∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
      volumeWeightedInvGram A J).trace = _
  rw [inverseGramExpectation A hA, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- Finite Markov inequality: the weighted mass of coordinates with
`w i * t < x i` is at most `t⁻¹ ∑ x`. -/
lemma weightedMarkov {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (_hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ}
    (ht : 0 < t) :
    ∑ i ∈ s.filter (fun i => w i * t < x i), w i ≤
      t⁻¹ * ∑ i ∈ s, x i := by
  classical
  have hfilter :
      ∑ i ∈ s.filter (fun i => w i * t < x i), w i ≤
        t⁻¹ * ∑ i ∈ s.filter (fun i => w i * t < x i), x i := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hxlt : w i * t < x i := (mem_filter.mp hi).2
    exact (le_inv_mul_iff₀ ht).mpr hxlt.le
  refine hfilter.trans ?_
  have hxsum :
      ∑ i ∈ s.filter (fun i => w i * t < x i), x i ≤ ∑ i ∈ s, x i :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i hi _ =>
      hx i hi
  exact mul_le_mul_of_nonneg_left hxsum (inv_nonneg.mpr ht.le)

/-- The event that the adjugate-trace proxy for `‖A_J⁻¹‖_F²` exceeds `t`.
On invertible blocks this is `volumeWeight(J) * t < det(A_J)² ‖A_J⁻¹‖_F²`,
i.e. `t < ‖A_J⁻¹‖_F²`. -/
def invFrobExceeds {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (t : ℝ)
    (J : Finset (Fin n)) : Prop :=
  volumeWeight A J * t < invFrobWeight A J

/-- Milestone D: finite high-probability inverse-Frobenius bound.

The volume mass of `k`-sets with
`‖A_J⁻¹‖_F² > k(n-k+1)/δ` (read via adjugate traces) is at most `δ`.
This implies the spectral-norm tail in Theorem R1 on the invertible
locus, since `‖·‖_2 ≤ ‖·‖_F`. -/
theorem markovInvFrob {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (invFrobExceeds A
          (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J ≤ δ := by
  classical
  set E := (k : ℝ) * ((n + 1 - k : ℕ) : ℝ)
  set t := E / δ
  have hx : ∀ J ∈ (univ : Finset (Fin n)).powersetCard k,
      0 ≤ invFrobWeight A J := fun _ _ => invFrobWeight_nonneg _ _
  have hw : ∀ J ∈ (univ : Finset (Fin n)).powersetCard k,
      0 ≤ volumeWeight A J := fun _ _ => volumeWeight_nonneg _ _
  have hsum := expectedInvFrobSq A hA
  by_cases hE : 0 < E
  · have ht : 0 < t := div_pos hE hδ
    have := weightedMarkov ((univ : Finset (Fin n)).powersetCard k)
      (volumeWeight A) (invFrobWeight A) hw hx ht
    refine this.trans ?_
    have : t⁻¹ * ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
        invFrobWeight A J = δ := by
      rw [hsum, show t⁻¹ = δ / E from inv_div, div_mul_cancel₀ _ (ne_of_gt hE)]
    exact this.le
  · have hEnonneg : 0 ≤ E := by
      simpa [hsum] using
        sum_nonneg fun J hJ => invFrobWeight_nonneg (k := k) (n := n) A J
    have hE0 : E = 0 := le_antisymm (le_of_not_gt hE) hEnonneg
    have hx0 : ∀ J ∈ (univ : Finset (Fin n)).powersetCard k,
        invFrobWeight A J = 0 := by
      intro J hJ
      exact (sum_eq_zero_iff_of_nonneg hx).1 (hsum.trans hE0) J hJ
    refine (sum_eq_zero ?_).trans_le (le_of_lt hδ)
    intro J hJ
    have hJuniv : J ∈ (univ : Finset (Fin n)).powersetCard k :=
      (mem_filter.mp hJ).1
    have hxlt : volumeWeight A J * t < invFrobWeight A J :=
      (mem_filter.mp hJ).2
    have : (0 : ℝ) < 0 := by
      simpa [hx0 J hJuniv, hE0, t] using hxlt
    exact (lt_irrefl (0 : ℝ) this).elim

end StructuredColumnSelection
