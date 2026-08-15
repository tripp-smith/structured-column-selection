import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.PrincipalColumns
import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds

namespace StructuredColumnSelection

open Classical
open Matrix Finset

/-- Milestone A theorem: transpose correspondence of orthogonality structure. -/
theorem milestoneA_transpose_correspondence {n k : ℕ}
    (Q : Matrix (Fin n) (Fin k) ℝ) :
    OrthogonalRows (Qᵀ) ↔ OrthogonalColumns Q :=
  orthogonalRows_transpose_iff Q

/-- Milestone A helper: selected-column square is definitionally a submatrix. -/
theorem milestoneA_selectedSquare_entry {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) (i j : Fin k) :
    SelectedSquare A J i j = A i (J j) :=
  selectedSquare_apply A J i j

/-- Milestone A helper: selected Gram matrix matches the product form. -/
theorem milestoneA_selectedGram_formula {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Fin k → Fin n) :
    SelectedGram A J = SelectedSquare A J * ((SelectedSquare A J)ᵀ) :=
  selectedGram_eq A J

/-- Milestone B: size-`k` volume weights of an orthogonal-row matrix sum to `1`. -/
theorem milestoneB_volume_normalization {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeight A J = 1 :=
  volumeWeights_sum_eq_one A hA

/-- Finite Cauchy–Binet identity used by Milestone B. -/
theorem milestoneB_cauchyBinet {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ S : { s : Finset (Fin n) // s.card = k },
        (colsSubmatrix A S.1 S.2).det * (rowsSubmatrix B S.1 S.2).det :=
  det_mul_cauchyBinet A B

/-- Milestone C: the finite inverse-Gram identity, via adjugates. -/
theorem milestoneC_inverse_gram_expectation {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      ((n + 1 - k : ℕ) : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) :=
  inverseGramExpectation A hA

/-- Milestone C helper: the same identity without orthogonality. -/
theorem milestoneC_adjugate_sum {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      ((n + 1 - k : ℕ) : R) • Matrix.adjugate (A * Aᵀ) :=
  volumeWeightedInvGrams_sum A

/-- Milestone D: volume-weighted inverse-Frobenius energy is `k(n-k+1)`. -/
theorem milestoneD_expected_inv_frob_sq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, invFrobWeight A J =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ) :=
  expectedInvFrobSq A hA

/-- Milestone D: finite Markov tail for the inverse-Frobenius proxy. -/
theorem milestoneD_markov_inv_frob {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) {δ : ℝ}
    (hδ : 0 < δ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (invFrobExceeds A
          (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J ≤ δ :=
  markovInvFrob A hA hδ

end StructuredColumnSelection
