import Mathlib

namespace StructuredColumnSelection

open Matrix

/-- Orthogonal-row structure for `A : ℝ^{k×n}`. -/
def OrthogonalRows {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) : Prop :=
  A * Aᵀ = 1

/-- Orthogonal-column structure for `Q : ℝ^{n×k}`. -/
def OrthogonalColumns {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  Qᵀ * Q = 1

/-- Column-Gram projector associated with `A`. -/
def ColumnProjector {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * A

end StructuredColumnSelection
