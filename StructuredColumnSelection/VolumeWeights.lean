import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.OrthogonalRows

/-!
# Volume weights

Squared maximal minors `det(A_J)²` for `|J| = k`. Under
`OrthogonalRows A` these form a finitely supported probability
distribution by Cauchy–Binet.
-/

namespace StructuredColumnSelection

open Matrix Finset

variable {R : Type*} [CommRing R]

/-- Squared volume of the column set `J`. Zero unless `#J = k`. -/
def volumeWeight {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : R :=
  if h : J.card = k then (colsSubmatrix A J h).det ^ 2 else 0

theorem volumeWeight_eq {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    {J : Finset (Fin n)} (h : J.card = k) :
    volumeWeight A J = (colsSubmatrix A J h).det ^ 2 :=
  dif_pos h

theorem volumeWeight_eq_selectedSquare {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) {J : Finset (Fin n)} (h : J.card = k) :
    volumeWeight A J = (SelectedSquare A (J.orderEmbOfFin h)).det ^ 2 := by
  rw [volumeWeight_eq A h, colsSubmatrix_eq_selectedSquare]

/-- Finite Cauchy–Binet specialisation: the volume weights sum to
`det(A Aᵀ)`. -/
theorem volumeWeights_sum_eq_det_mul_transpose {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeight A J =
      (A * Aᵀ).det := by
  rw [det_mul_cauchyBinet_powersetCard]
  refine sum_congr rfl fun J hJ => ?_
  have h : J.card = k := (mem_powersetCard.mp hJ).2
  simp only [volumeWeight, h, ↓reduceDIte, colsSubmatrix, rowsSubmatrix, sq]
  have hT :
      (Aᵀ).submatrix (J.orderEmbOfFin h) id =
        (A.submatrix id (J.orderEmbOfFin h))ᵀ := by
    ext i j
    simp [submatrix_apply, transpose_apply]
  rw [hT, det_transpose]

/-- Milestone B: orthogonal rows normalise the volume weights to `1`. -/
theorem volumeWeights_sum_eq_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeight A J = 1 := by
  rw [volumeWeights_sum_eq_det_mul_transpose, hA, det_one]

end StructuredColumnSelection
