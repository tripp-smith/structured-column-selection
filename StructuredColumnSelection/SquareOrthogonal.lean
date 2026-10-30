import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.PrefixInverse

/-!
# Square orthogonal-row CPQR

On a square orthogonal-row matrix the columns are orthonormal, the CPQR
set is every column, and the selected Gram is the identity, so the
inverse trace equals `k` exactly. Phase AR's upper bound
`(k : ℝ) - 2 + 2 / (1 - ρ ^ 2)` is valid and equals `k` at `ρ = 0`,
which is admissible because column inner products vanish. This is not a
bound for rectangular matrices. It does not close outcome 3. It is not
a polynomial theorem for every orthogonal-row matrix.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

/-- On a square orthogonal-row matrix the columns are orthonormal, the
CPQR set is every column, and the selected Gram is the identity, so the
inverse trace equals `k` exactly. Phase AR's upper bound
`(k : ℝ) - 2 + 2 / (1 - ρ ^ 2)` is valid and equals `k` at `ρ = 0`,
which is admissible because column inner products vanish. This is not a
bound for rectangular matrices. It does not close outcome 3. It is not
a polynomial theorem for every orthogonal-row matrix. -/
theorem square_cpqr_trace_eq {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : OrthogonalRows A) :
    cpqrSet A = univ ∧
      selectedColGram A (cpqrSet A) = 1 ∧
      ((selectedColGram A (cpqrSet A))⁻¹).trace = (k : ℝ) ∧
      ∀ x : Fin (cpqrSet A).card → ℝ,
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) = vecEnergy x := by
  have hATA : Aᵀ * A = 1 := mul_eq_one_comm.mp (show A * Aᵀ = 1 from hA)
  have hcard : (cpqrSet A).card = k := cpqrSet_card_eq A hA
  have huniv : cpqrSet A = univ :=
    (card_eq_iff_eq_univ (cpqrSet A)).mp (hcard.trans (Fintype.card_fin k).symm)
  have hgramUniv : selectedColGram A (univ : Finset (Fin k)) = 1 := by
    let e := (univ : Finset (Fin k)).orderEmbOfFin rfl
    ext i j
    rw [Matrix.one_apply]
    have hdot :
        selectedColGram A (univ : Finset (Fin k)) i j =
          (Aᵀ * A) (e i) (e j) := by
      calc
        selectedColGram A (univ : Finset (Fin k)) i j
            = ∑ r : Fin k,
                (selectedCols A (univ : Finset (Fin k)))ᵀ i r *
                  selectedCols A (univ : Finset (Fin k)) r j := by
              rw [selectedColGram, Matrix.mul_apply]
          _ = ∑ r : Fin k, A r (e i) * A r (e j) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Matrix.transpose_apply, selectedCols, Matrix.submatrix_apply,
                Matrix.submatrix_apply, id_eq]
          _ = (Aᵀ * A) (e i) (e j) := by
              rw [Matrix.mul_apply]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Matrix.transpose_apply]
    rw [hdot, hATA, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (e.injective.ne hij), if_neg hij]
  have hgram : selectedColGram A (cpqrSet A) = 1 := by
    rw [huniv]
    exact hgramUniv
  refine ⟨huniv, hgram, ?_, ?_⟩
  · have hinv : (selectedColGram A (cpqrSet A))⁻¹ = 1 := by
      rw [hgram]
      exact inv_one
    rw [hinv, Matrix.trace_one, Fintype.card_fin, hcard]
  · intro x
    have hBB :
        (selectedCols A (cpqrSet A))ᵀ * selectedCols A (cpqrSet A) = 1 :=
      hgram
    calc
      vecEnergy (selectedCols A (cpqrSet A) *ᵥ x)
          = (selectedCols A (cpqrSet A) *ᵥ x) ⬝ᵥ
              (selectedCols A (cpqrSet A) *ᵥ x) :=
        vecEnergy_eq_dot _
      _ = ((selectedCols A (cpqrSet A))ᵀ *ᵥ
            (selectedCols A (cpqrSet A) *ᵥ x)) ⬝ᵥ x :=
        (transpose_mulVec_dot _ _ _).symm
      _ = (((selectedCols A (cpqrSet A))ᵀ *
            selectedCols A (cpqrSet A)) *ᵥ x) ⬝ᵥ x := by
        rw [← mulVec_mul_eq]
      _ = x ⬝ᵥ x := by rw [hBB, one_mulVec_eq]
      _ = vecEnergy x := (vecEnergy_eq_dot x).symm

end StructuredColumnSelection
