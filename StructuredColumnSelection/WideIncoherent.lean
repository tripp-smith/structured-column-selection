import StructuredColumnSelection.WideCPQRGrowth
import StructuredColumnSelection.StaticClass

/-!
# The adverse family is not pairwise orthogonal

Phase P bounds CPQR on `ColumnIncoherent A 0`. The outcome-2 frame is
outside that class: its leading triangular columns have inner product
`-wideC m * (wideDiagNat m 0) ^ 2`, which is nonzero for every `m ≥ 2`.

This does not close outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

lemma wide_prefix_col_inner {m : ℕ} (hm : 2 ≤ m)
    (A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ)
    (htri : ∀ i j : Fin (wideDim m),
      A i (j.castAdd (wideDim m * wideRepeats m)) = wideTriangular m i j) :
    colInner A
        ((⟨0, by have h2 := wide_two_le_dim hm; omega⟩ : Fin (wideDim m)).castAdd
          (wideDim m * wideRepeats m))
        ((⟨1, by have h2 := wide_two_le_dim hm; omega⟩ : Fin (wideDim m)).castAdd
          (wideDim m * wideRepeats m)) =
      -(wideC m) * (wideDiagNat m 0) ^ 2 := by
  let j0 : Fin (wideDim m) := ⟨0, by have h2 := wide_two_le_dim hm; omega⟩
  let j1 : Fin (wideDim m) := ⟨1, by have h2 := wide_two_le_dim hm; omega⟩
  have hsum : colInner A (j0.castAdd _) (j1.castAdd _) =
      ∑ i : Fin (wideDim m), wideTriangular m i j0 * wideTriangular m i j1 := by
    simp only [colInner, htri]
  have honly : ∑ i : Fin (wideDim m), wideTriangular m i j0 * wideTriangular m i j1 =
      wideTriangular m j0 j0 * wideTriangular m j0 j1 := by
    refine Finset.sum_eq_single j0 ?_ ?_
    · intro i _ hi
      have hcol : wideTriangular m i j0 = 0 := by
        have hlt : ¬ (i : ℕ) < (j0 : ℕ) := by simp [j0]
        simp [wideTriangular, hi, hlt]
      simp [hcol]
    · intro hj
      exact (hj (mem_univ j0)).elim
  have h00 : wideTriangular m j0 j0 = wideDiagNat m 0 := by
    simp [wideTriangular, j0, wideDiagNat, pow_zero]
  have hne : j0 ≠ j1 := by
    intro h
    have := congrArg (fun i : Fin (wideDim m) => (i : ℕ)) h
    simp [j0, j1] at this
  have hlt : (j0 : ℕ) < (j1 : ℕ) := by simp [j0, j1]
  have h01 : wideTriangular m j0 j1 = -wideC m * wideDiagNat m 0 := by
    simp [wideTriangular, hne, hlt, j0, wideDiagNat, pow_zero]
  rw [hsum, honly, h00, h01]
  ring

lemma wide_prefix_inner_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    -(wideC m) * (wideDiagNat m 0) ^ 2 ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · exact neg_ne_zero.mpr (ne_of_gt (wideC_pos hm))
  · exact pow_ne_zero 2 (ne_of_gt (wideDiag_pos hm 0))

theorem wide_not_incoherent_zero {m : ℕ} (hm : 2 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideWidth m)) ℝ,
      OrthogonalRows A ∧ ¬ ColumnIncoherent A 0 := by
  obtain ⟨A, _, horth, htri, _⟩ := wide_adverse_family hm
  refine ⟨A, horth, ?_⟩
  intro hC
  let j0 : Fin (wideDim m) := ⟨0, by have h2 := wide_two_le_dim hm; omega⟩
  let j1 : Fin (wideDim m) := ⟨1, by have h2 := wide_two_le_dim hm; omega⟩
  have hne : j0.castAdd (wideDim m * wideRepeats m) ≠
      j1.castAdd (wideDim m * wideRepeats m) := by
    intro h
    have := congrArg (fun i : Fin (wideWidth m) => (i : ℕ)) h
    simp [j0, j1, Fin.castAdd] at this
  have hzero := abs_eq_zero.mp
    (le_antisymm (hC _ _ hne) (abs_nonneg _))
  rw [wide_prefix_col_inner hm A htri] at hzero
  exact wide_prefix_inner_ne_zero hm hzero

end StructuredColumnSelection
