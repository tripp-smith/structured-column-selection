import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.OrthogonalRows
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Inverse-Gram expectation

Finite identity underlying Milestone C. The summand is an adjugate so it
remains defined when `A_J` is singular; on the invertible locus this is
`det(A_J)² • (A_J A_Jᵀ)⁻¹`.

The general algebraic form is

`∑_{#J=k} adj(A_J A_Jᵀ) = (n + 1 - k) • adj(A Aᵀ)`.

Orthogonal rows specialise the right-hand side to `(n + 1 - k) • I`.
-/

namespace StructuredColumnSelection

open Equiv Finset Function

variable {R : Type*} [CommRing R]

/-- Volume-weighted inverse Gram, as an adjugate. -/
def volumeWeightedInvGram {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : Matrix (Fin k) (Fin k) R :=
  if h : J.card = k then
    Matrix.adjugate (colsSubmatrix A J h * (colsSubmatrix A J h)ᵀ)
  else
    0

theorem volumeWeightedInvGram_eq {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    {J : Finset (Fin n)} (h : J.card = k) :
    volumeWeightedInvGram A J =
      Matrix.adjugate (colsSubmatrix A J h * (colsSubmatrix A J h)ᵀ) :=
  dif_pos h

/-- Complementary `(k-1)`-minor, or `0` unless `#T = k-1`. -/
def complementaryMinor {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) R)
    (i : Fin (m + 1)) (T : Finset (Fin n)) : R :=
  if h : T.card = m then
    (A.submatrix i.succAbove (T.orderEmbOfFin h)).det
  else
    0

lemma complementaryMinor_eq {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) R)
    (i : Fin (m + 1)) {T : Finset (Fin n)} (h : T.card = m) :
    complementaryMinor A i T = (A.submatrix i.succAbove (T.orderEmbOfFin h)).det :=
  dif_pos h

lemma submatrix_mul {l n m ι κ : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix l n R) (Y : Matrix n m R) (f : ι → l) (g : κ → m) :
    (X * Y).submatrix f g = X.submatrix f id * Y.submatrix id g := by
  ext a b
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

lemma submatrix_mul_transpose {l n ι κ : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix l n R) (f : ι → l) (g : κ → l) :
    (X * Xᵀ).submatrix f g = X.submatrix f id * (X.submatrix g id)ᵀ := by
  rw [submatrix_mul]
  ext a b
  simp [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.mul_apply]

lemma selectedGram_submatrix_succAbove {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (α β : Fin (m + 1)) :
    ((colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ).submatrix
        β.succAbove α.succAbove) =
      A.submatrix β.succAbove (J.orderEmbOfFin hJ) *
        (A.submatrix α.succAbove (J.orderEmbOfFin hJ))ᵀ := by
  rw [submatrix_mul_transpose]
  ext a b
  simp [colsSubmatrix, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply]

def embedSubset {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (S : Finset (Fin (m + 1))) : Finset (Fin n) :=
  S.map (J.orderEmbOfFin hJ).toEmbedding

lemma embedSubset_card {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (S : Finset (Fin (m + 1))) : (embedSubset J hJ S).card = S.card :=
  card_map _

lemma embedSubset_subset {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (S : Finset (Fin (m + 1))) : embedSubset J hJ S ⊆ J := by
  intro x hx
  rcases mem_map.mp hx with ⟨_, _, rfl⟩
  exact J.orderEmbOfFin_mem hJ _

lemma embedSubset_mem_powersetCard {m n : ℕ} (J : Finset (Fin n))
    (hJ : J.card = m + 1) (S : Finset (Fin (m + 1))) (hS : S.card = m) :
    embedSubset J hJ S ∈ J.powersetCard m :=
  mem_powersetCard.mpr ⟨embedSubset_subset J hJ S, by rw [embedSubset_card, hS]⟩

lemma orderEmb_embedSubset {m n : ℕ} (J : Finset (Fin n))
    (hJ : J.card = m + 1) (S : Finset (Fin (m + 1))) (hS : S.card = m) :
    (fun i => J.orderEmbOfFin hJ (S.orderEmbOfFin hS i)) =
      (embedSubset J hJ S).orderEmbOfFin (by rw [embedSubset_card, hS]) := by
  refine orderEmbOfFin_unique (by rw [embedSubset_card, hS]) ?_ ?_
  · intro i
    exact embedSubset_subset J hJ S (orderEmbOfFin_mem _ _ _)
  · exact (J.orderEmbOfFin hJ).strictMono.comp (S.orderEmbOfFin hS).strictMono

lemma complementaryMinor_embed {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (S : Finset (Fin (m + 1))) (hS : S.card = m)
    (i : Fin (m + 1)) :
    complementaryMinor A i (embedSubset J hJ S) =
      (A.submatrix i.succAbove fun j =>
        J.orderEmbOfFin hJ (S.orderEmbOfFin hS j)).det := by
  rw [complementaryMinor_eq A i (by rw [embedSubset_card, hS]),
    ← orderEmb_embedSubset J hJ S hS]

lemma colsSubmatrix_comp_orderEmb {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (S : Finset (Fin (m + 1))) (hS : S.card = m)
    (β : Fin (m + 1)) :
    colsSubmatrix (A.submatrix β.succAbove (J.orderEmbOfFin hJ)) S hS =
      A.submatrix β.succAbove fun j =>
        J.orderEmbOfFin hJ (S.orderEmbOfFin hS j) := by
  ext a b
  simp [colsSubmatrix, Matrix.submatrix_apply]

lemma rowsSubmatrix_transpose_comp {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (S : Finset (Fin (m + 1))) (hS : S.card = m)
    (α : Fin (m + 1)) :
    rowsSubmatrix ((A.submatrix α.succAbove (J.orderEmbOfFin hJ))ᵀ) S hS =
      (A.submatrix α.succAbove fun j =>
        J.orderEmbOfFin hJ (S.orderEmbOfFin hS j))ᵀ := by
  ext a b
  simp [rowsSubmatrix, Matrix.submatrix_apply, Matrix.transpose_apply]

lemma det_selectedGram_rowDeleted {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (α β : Fin (m + 1)) :
    ((colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ).submatrix
        β.succAbove α.succAbove).det =
      ∑ S : { s : Finset (Fin (m + 1)) // s.card = m },
        complementaryMinor A β (embedSubset J hJ S.1) *
          complementaryMinor A α (embedSubset J hJ S.1) := by
  rw [selectedGram_submatrix_succAbove, det_mul_cauchyBinet]
  refine Fintype.sum_congr _ _ fun S => ?_
  rw [complementaryMinor_embed A J hJ S.1 S.2,
    complementaryMinor_embed A J hJ S.1 S.2]
  simp [colsSubmatrix_comp_orderEmb, rowsSubmatrix_transpose_comp,
    Matrix.det_transpose]

def unembedSubset {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (T : Finset (Fin n)) : Finset (Fin (m + 1)) :=
  univ.filter fun i => J.orderEmbOfFin hJ i ∈ T

lemma embed_unembed {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (T : Finset (Fin n)) (hTJ : T ⊆ J) :
    embedSubset J hJ (unembedSubset J hJ T) = T := by
  ext x
  simp [embedSubset, unembedSubset, mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    have hxJ : x ∈ J := hTJ hx
    have : x ∈ image (J.orderEmbOfFin hJ) univ := by
      rw [image_orderEmbOfFin_univ]
      exact hxJ
    rcases mem_image.mp this with ⟨i, _, rfl⟩
    exact ⟨i, by simpa [unembedSubset] using hx, rfl⟩

lemma unembed_embed {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (S : Finset (Fin (m + 1))) :
    unembedSubset J hJ (embedSubset J hJ S) = S := by
  ext i
  simp [unembedSubset, embedSubset, mem_map, (J.orderEmbOfFin hJ).injective.eq_iff]

lemma unembedSubset_card {m n : ℕ} (J : Finset (Fin n)) (hJ : J.card = m + 1)
    (T : Finset (Fin n)) (hTJ : T ⊆ J) :
    (unembedSubset J hJ T).card = T.card := by
  rw [← embedSubset_card J hJ, embed_unembed J hJ T hTJ]

lemma sum_local_minors {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) R)
    (J : Finset (Fin n)) (hJ : J.card = m + 1) (α β : Fin (m + 1)) :
    ∑ S : { s : Finset (Fin (m + 1)) // s.card = m },
        complementaryMinor A β (embedSubset J hJ S.1) *
          complementaryMinor A α (embedSubset J hJ S.1) =
      ∑ T ∈ J.powersetCard m,
        complementaryMinor A β T * complementaryMinor A α T := by
  change
      ∑ S ∈ (univ : Finset { s : Finset (Fin (m + 1)) // s.card = m }),
        complementaryMinor A β (embedSubset J hJ S.1) *
          complementaryMinor A α (embedSubset J hJ S.1) = _
  refine Finset.sum_bij'
      (fun S _ => embedSubset J hJ S.1)
      (fun T hT =>
        ⟨unembedSubset J hJ T,
          by
            rw [unembedSubset_card J hJ T (mem_powersetCard.mp hT).1,
              (mem_powersetCard.mp hT).2]⟩)
      (fun S _ => embedSubset_mem_powersetCard J hJ S.1 S.2)
      (fun _ _ => mem_univ _)
      (fun S _ => by simp [unembed_embed])
      (fun T hT => embed_unembed J hJ T (mem_powersetCard.mp hT).1)
      (fun _ _ => rfl)

lemma card_extensions {m n : ℕ} (T : Finset (Fin n)) (hT : T.card = m) :
    #(((univ : Finset (Fin n)).powersetCard (m + 1)).filter (T ⊆ ·)) =
      n + 1 - (m + 1) := by
  have hle : T.card ≤ m + 1 := by omega
  rw [card_filter_powersetCard_subset T univ (m + 1) (subset_univ T) hle]
  simp [hT, Fintype.card_fin, Nat.choose_one_right]
  omega

lemma sum_nested_minors {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) R)
    (α β : Fin (m + 1)) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard (m + 1),
        ∑ T ∈ J.powersetCard m,
          complementaryMinor A β T * complementaryMinor A α T =
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard m,
        ∑ J ∈ ((univ : Finset (Fin n)).powersetCard (m + 1)).filter (T ⊆ ·),
          complementaryMinor A β T * complementaryMinor A α T := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij'
      (fun p _ => ⟨p.2, p.1⟩)
      (fun q _ => ⟨q.2, q.1⟩)
      (fun p hp => by
        rw [mem_sigma] at hp ⊢
        exact ⟨mem_powersetCard.mpr ⟨subset_univ _, (mem_powersetCard.mp hp.2).2⟩,
          mem_filter.mpr ⟨hp.1, (mem_powersetCard.mp hp.2).1⟩⟩)
      (fun q hq => by
        rw [mem_sigma] at hq ⊢
        exact ⟨(mem_filter.mp hq.2).1,
          mem_powersetCard.mpr ⟨(mem_filter.mp hq.2).2,
            (mem_powersetCard.mp hq.1).2⟩⟩)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun _ _ => rfl)

lemma sum_extensions_const {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) R)
    (α β : Fin (m + 1)) :
    ∑ T ∈ (univ : Finset (Fin n)).powersetCard m,
        ∑ J ∈ ((univ : Finset (Fin n)).powersetCard (m + 1)).filter (T ⊆ ·),
          complementaryMinor A β T * complementaryMinor A α T =
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard m,
        (n + 1 - (m + 1) : R) *
          (complementaryMinor A β T * complementaryMinor A α T) := by
  refine sum_congr rfl fun T hT => ?_
  have hTcard : T.card = m := (mem_powersetCard.mp hT).2
  rw [sum_const, card_extensions T hTcard, nsmul_eq_mul]

lemma det_rowDeleted_cauchyBinet {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (α β : Fin (m + 1)) :
    (A.submatrix β.succAbove id * (A.submatrix α.succAbove id)ᵀ).det =
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard m,
        complementaryMinor A β T * complementaryMinor A α T := by
  rw [det_mul_cauchyBinet_powersetCard]
  refine sum_congr rfl fun T hT => ?_
  have h : T.card = m := (mem_powersetCard.mp hT).2
  simp [complementaryMinor, colsSubmatrix, rowsSubmatrix, h, Matrix.det_transpose]

lemma det_rowDeleted_eq_adjugate_minor {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (α β : Fin (m + 1)) :
    (A.submatrix β.succAbove id * (A.submatrix α.succAbove id)ᵀ).det =
      ((A * Aᵀ).submatrix β.succAbove α.succAbove).det := by
  rw [submatrix_mul_transpose]

lemma adjugate_selectedGram_apply {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (α β : Fin (m + 1)) :
    Matrix.adjugate (colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ) α β =
      (-1) ^ (β + α : ℕ) *
        ∑ S : { s : Finset (Fin (m + 1)) // s.card = m },
          complementaryMinor A β (embedSubset J hJ S.1) *
            complementaryMinor A α (embedSubset J hJ S.1) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, det_selectedGram_rowDeleted]

lemma volumeWeightedInvGrams_sum_succ_apply {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) (α β : Fin (m + 1)) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard (m + 1),
        volumeWeightedInvGram A J α β =
      (n + 1 - (m + 1) : R) * Matrix.adjugate (A * Aᵀ) α β := by
  have hexpand :
      ∑ J ∈ (univ : Finset (Fin n)).powersetCard (m + 1),
          volumeWeightedInvGram A J α β =
        (-1) ^ (β + α : ℕ) *
          ∑ J ∈ (univ : Finset (Fin n)).powersetCard (m + 1),
            ∑ T ∈ J.powersetCard m,
              complementaryMinor A β T * complementaryMinor A α T := by
    rw [← mul_sum]
    refine sum_congr rfl fun J hJ => ?_
    have hcard : J.card = m + 1 := (mem_powersetCard.mp hJ).2
    rw [volumeWeightedInvGram_eq A hcard, adjugate_selectedGram_apply A J hcard,
      sum_local_minors A J hcard]
  rw [hexpand, sum_nested_minors, sum_extensions_const, ← mul_sum,
    ← det_rowDeleted_cauchyBinet, det_rowDeleted_eq_adjugate_minor,
    ← Matrix.adjugate_fin_succ_eq_det_submatrix]
  ring

lemma volumeWeightedInvGrams_sum_succ {m n : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard (m + 1), volumeWeightedInvGram A J =
      (n + 1 - (m + 1) : R) • (A * Aᵀ).adjugate := by
  ext α β
  simpa [Matrix.smul_apply] using volumeWeightedInvGrams_sum_succ_apply A α β

lemma volumeWeightedInvGrams_sum_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard 0, volumeWeightedInvGram A J =
      (n + 1 - 0 : R) • (A * Aᵀ).adjugate :=
  Subsingleton.elim _ _

/-- Finite inverse-Gram identity, without an orthogonality hypothesis. -/
theorem volumeWeightedInvGrams_sum {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      (n + 1 - k : R) • (A * Aᵀ).adjugate := by
  cases k with
  | zero => exact volumeWeightedInvGrams_sum_zero A
  | succ m => exact volumeWeightedInvGrams_sum_succ A

/-- Milestone C: orthogonal rows make the inverse-Gram sum a multiple of `I`. -/
theorem inverseGramExpectation {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeightedInvGram A J =
      (n + 1 - k : ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [volumeWeightedInvGrams_sum, hA, Matrix.adjugate_one]

end StructuredColumnSelection
