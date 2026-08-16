import StructuredColumnSelection.ResidualEnergy
import StructuredColumnSelection.CPQRVolume
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Contraction and last-residual control

An orthogonal-row matrix is a contraction in Euclidean energy, so
every column has leverage at most `1`. The last CPQR residual is at
least `1 / (n-k+1)`.

These constrain the residual-to-`σ_min` gap but are not a joint
`poly(n,k)` inverse-norm bound. They do not close Milestone E. The
simplex ETF shows that a universal improvement of `1/C(n,k)` or
`σ_min ≥ |det|` is false; a prefix-orthonormal inverse-Frobenius
bound remains the next formal target.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-- Euclidean energy `∑ vᵢ²`. -/
def vecEnergy {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, v i ^ 2

lemma vecEnergy_eq_dot {m : ℕ} (v : Fin m → ℝ) :
    vecEnergy v = v ⬝ᵥ v := by
  simp only [vecEnergy, dotProduct_eq, pow_two]

lemma vecEnergy_nonneg {m : ℕ} (v : Fin m → ℝ) :
    0 ≤ vecEnergy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma energy_cauchy {m : ℕ} (v w : Fin m → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ vecEnergy v * vecEnergy w := by
  simpa [vecEnergy, dotProduct_eq, pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin m)) v w)

lemma orthogonalRows_mulVec_AAT {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (y : Fin k → ℝ) :
    A *ᵥ (Aᵀ *ᵥ y) = y := by
  have : (A * Aᵀ) *ᵥ y = y := by
    rw [show A * Aᵀ = (1 : Matrix (Fin k) (Fin k) ℝ) from hA, one_mulVec_eq]
  rw [mulVec_mul_eq] at this
  exact this

lemma vecEnergy_transpose_mulVec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (y : Fin k → ℝ) :
    vecEnergy (Aᵀ *ᵥ y) = vecEnergy y := by
  rw [vecEnergy_eq_dot, vecEnergy_eq_dot]
  have h := transpose_mulVec_dot A y (Aᵀ *ᵥ y)
  have hy : A *ᵥ (Aᵀ *ᵥ y) = y := orthogonalRows_mulVec_AAT A hA y
  have : ((Aᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ y)) = (y ⬝ᵥ (A *ᵥ (Aᵀ *ᵥ y))) := h
  simpa [hy] using this

/-- Orthogonal-row matrices are contractions in Euclidean energy.

This is not an inverse-norm bound. -/
theorem mulVec_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (x : Fin n → ℝ) :
    vecEnergy (A *ᵥ x) ≤ vecEnergy x := by
  set y : Fin k → ℝ := A *ᵥ x
  have hdot : (Aᵀ *ᵥ y) ⬝ᵥ x = vecEnergy y := by
    have h := transpose_mulVec_dot A y x
    rw [vecEnergy_eq_dot]
    simpa [y] using h
  have hcs := energy_cauchy (Aᵀ *ᵥ y) x
  have htr := vecEnergy_transpose_mulVec A hA y
  have : vecEnergy y ^ 2 ≤ vecEnergy y * vecEnergy x := by
    rw [hdot, htr] at hcs
    exact hcs
  nlinarith [vecEnergy_nonneg y, vecEnergy_nonneg x]

/-- Every column of an orthogonal-row matrix has leverage at most `1`. -/
theorem col_energy_le {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) (j : Fin n) :
    vecEnergy (fun i => A i j) ≤ 1 := by
  let x : Fin n → ℝ := fun j' => if j' = j then (1 : ℝ) else 0
  have hx : vecEnergy x = 1 := by
    simp only [vecEnergy]
    rw [Finset.sum_eq_single j]
    · simp [x]
    · intro j' _ hj
      simp [x, hj]
    · intro h
      exact (h (mem_univ j)).elim
  have hAx : A *ᵥ x = fun i => A i j := by
    ext i
    simp only [mulVec_sum_eq, x]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj
      simp [hj]
    · intro h
      exact (h (mem_univ j)).elim
  have := mulVec_energy_le A hA x
  simpa [hAx, hx] using this

/-- Last CPQR residual is at least the complementary-rank average
`1 / (n-k+1)`. This is not an inverse-norm bound. -/
theorem lastResidual_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 0 < k) :
    (1 : ℝ) / ((n : ℝ) - ((k - 1 : ℕ) : ℝ)) ≤
      residualSq A (cpqrIterate A (k - 1))
        (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)) := by
  have ht : k - 1 < k := Nat.sub_one_lt_of_lt hk
  have h := cpqr_pivot_residual_ge A hA ht
  have hsub : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hk)]
      norm_num
    rw [this]
    ring
  simpa [hsub, one_div] using h

end StructuredColumnSelection
