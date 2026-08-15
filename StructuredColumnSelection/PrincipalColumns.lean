import StructuredColumnSelection.Definitions

namespace StructuredColumnSelection

open Matrix

/-- Square matrix extracted by selecting `k` columns through an index map `J`. -/
def SelectedSquare {k n : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (A : Matrix (Fin k) (Fin n) 𝕜) (J : Fin k → Fin n) : Matrix (Fin k) (Fin k) 𝕜 :=
  A.submatrix id J

/-- Gram matrix of the selected square block. -/
def SelectedGram {k n : ℕ} {𝕜 : Type*} [Semiring 𝕜] [StarSemiring 𝕜]
    (A : Matrix (Fin k) (Fin n) 𝕜) (J : Fin k → Fin n) : Matrix (Fin k) (Fin k) 𝕜 :=
  SelectedSquare A J * (SelectedSquare A J)ᴴ

theorem selectedSquare_apply {k n : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (A : Matrix (Fin k) (Fin n) 𝕜) (J : Fin k → Fin n) (i j : Fin k) :
    SelectedSquare A J i j = A i (J j) := rfl

theorem selectedSquare_transpose {k n : ℕ} {𝕜 : Type*} [Semiring 𝕜]
    (A : Matrix (Fin k) (Fin n) 𝕜) (J : Fin k → Fin n) :
    (SelectedSquare A J)ᵀ = (Aᵀ).submatrix J id := rfl

theorem selectedSquare_det_eq_submatrix_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) :
    (SelectedSquare A J).det = (A.submatrix id J).det := rfl

theorem selectedGram_eq {k n : ℕ} {𝕜 : Type*} [Semiring 𝕜] [StarSemiring 𝕜]
    (A : Matrix (Fin k) (Fin n) 𝕜) (J : Fin k → Fin n) :
    SelectedGram A J = SelectedSquare A J * (SelectedSquare A J)ᴴ := rfl

end StructuredColumnSelection
