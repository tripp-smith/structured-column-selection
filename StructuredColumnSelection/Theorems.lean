import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.PrincipalColumns

namespace StructuredColumnSelection

/-- Milestone A theorem: transpose correspondence of orthogonality structure. -/
theorem milestoneA_transpose_correspondence {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) :
    OrthogonalRows Qᵀ ↔ OrthogonalColumns Q :=
  orthogonalRows_transpose_iff Q

/-- Milestone A helper: selected-column square is definitionally a submatrix. -/
theorem milestoneA_selectedSquare_entry {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) (i j : Fin k) :
    SelectedSquare A J i j = A i (J j) :=
  selectedSquare_apply A J i j

/-- Milestone A helper: selected Gram matrix matches the product form. -/
theorem milestoneA_selectedGram_formula {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) :
    SelectedGram A J = SelectedSquare A J * (SelectedSquare A J)ᴴ :=
  selectedGram_eq A J

end StructuredColumnSelection
