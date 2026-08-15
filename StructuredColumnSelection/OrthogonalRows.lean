import StructuredColumnSelection.Definitions

namespace StructuredColumnSelection

open Matrix

/--
Transpose correspondence for the structural class in `SPEC.md`:
`A Aᵀ = I` for `A = Qᵀ` is equivalent to `Qᵀ Q = I`.
-/
theorem orthogonalRows_transpose_iff {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ) :
    OrthogonalRows Qᵀ ↔ OrthogonalColumns Q := by
  unfold OrthogonalRows OrthogonalColumns
  simp

theorem orthogonalRows_of_transpose {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : OrthogonalColumns Q) :
    OrthogonalRows Qᵀ := (orthogonalRows_transpose_iff Q).2 hQ

theorem orthogonalColumns_of_transpose {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) (hA : OrthogonalRows Qᵀ) :
    OrthogonalColumns Q := (orthogonalRows_transpose_iff Q).1 hA

end StructuredColumnSelection
