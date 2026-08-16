import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.CPQRVolume
import StructuredColumnSelection.PrefixInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Inverse-Frobenius / leave-one-out residual identity (Milestone E, Path 1)

On an independent column set `J`, Cramer's rule for the selected Gram
`G_J = selectedColGram A J` gives the exact identity

```text
tr(G_J⁻¹) = (∑_{j ∈ J} det(G_{J \ {j}})) / det(G_J)
          = ∑_{j ∈ J} 1 / residualSq A (J.erase j) j.
```

When `#J = k` this is `‖A_J⁻¹‖_F²`, and it equals the Milestone D proxy
`invFrobWeight A J / volumeWeight A J`. The quadratic-form consequence

```text
‖x‖² ≤ ‖A_J x‖² · tr(G_J⁻¹)
```

is the elementary bound `σ_min(A_J) ≥ 1 / √tr(G_J⁻¹)`. This is the
`σ_min` side of the `σ_min / |det|` gap: it can beat `|det A_J|` on
unbalanced blocks, but it is **not** universally larger (the simplex
ETF saturates `σ_min = |det|`). It is **not** a joint `poly(n,k)`
inverse-norm bound: that would need a polynomial lower bound on every
leave-one-out residual of the CPQR set, which is not proved here.

This module does **not** close Milestone E.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-! ### Submatrix casts along `finCongr` -/

lemma det_submatrix_finCongr {t m : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (h : t = m) :
    (G.submatrix (finCongr h.symm) (finCongr h.symm)).det = G.det :=
  Matrix.det_submatrix_equiv_self (finCongr h.symm) G

lemma trace_submatrix_finCongr {t m : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (h : t = m) :
    (G.submatrix (finCongr h.symm) (finCongr h.symm)).trace = G.trace := by
  change (∑ i : Fin m, G (finCongr h.symm i) (finCongr h.symm i)) =
    ∑ j : Fin t, G j j
  exact Fintype.sum_equiv (finCongr h.symm)
    (fun i : Fin m => G (finCongr h.symm i) (finCongr h.symm i))
    (fun j : Fin t => G j j) fun _ => rfl

lemma submatrix_mul_finCongr {t m : ℕ}
    (A B : Matrix (Fin t) (Fin t) ℝ) (h : t = m) :
    (A * B).submatrix (finCongr h.symm) (finCongr h.symm) =
      A.submatrix (finCongr h.symm) (finCongr h.symm) *
        B.submatrix (finCongr h.symm) (finCongr h.symm) := by
  apply Matrix.ext
  intro i j
  change (∑ l : Fin t, A (finCongr h.symm i) l * B l (finCongr h.symm j)) =
    ∑ k : Fin m, A (finCongr h.symm i) (finCongr h.symm k) *
      B (finCongr h.symm k) (finCongr h.symm j)
  exact (Fintype.sum_equiv (finCongr h.symm)
    (fun k : Fin m => A (finCongr h.symm i) (finCongr h.symm k) *
      B (finCongr h.symm k) (finCongr h.symm j))
    (fun l : Fin t => A (finCongr h.symm i) l * B l (finCongr h.symm j))
    fun _ => rfl).symm

lemma one_submatrix_finCongr {t m : ℕ} (h : t = m) :
    (1 : Matrix (Fin t) (Fin t) ℝ).submatrix
        (finCongr h.symm) (finCongr h.symm) =
      (1 : Matrix (Fin m) (Fin m) ℝ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply,
    (finCongr h.symm).injective.eq_iff]

lemma inv_submatrix_finCongr {t m : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (h : t = m) (hG : G.det ≠ 0) :
    (G.submatrix (finCongr h.symm) (finCongr h.symm))⁻¹ =
      G⁻¹.submatrix (finCongr h.symm) (finCongr h.symm) := by
  apply Matrix.inv_eq_left_inv
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (Ne.isUnit hG)
  calc G⁻¹.submatrix (finCongr h.symm) (finCongr h.symm) *
        G.submatrix (finCongr h.symm) (finCongr h.symm)
      = (G⁻¹ * G).submatrix (finCongr h.symm) (finCongr h.symm) :=
        (submatrix_mul_finCongr G⁻¹ G h).symm
    _ = (1 : Matrix (Fin t) (Fin t) ℝ).submatrix
          (finCongr h.symm) (finCongr h.symm) := by rw [h1]
    _ = 1 := one_submatrix_finCongr h

/-- Selected Gram, reindexed to `Fin m` when `#J = m`. -/
noncomputable def selectedColGramCast {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m) : Matrix (Fin m) (Fin m) ℝ :=
  (selectedColGram A J).submatrix (finCongr hJ.symm) (finCongr hJ.symm)

lemma selectedColGramCast_det {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m) :
    (selectedColGramCast A J hJ).det = (selectedColGram A J).det :=
  det_submatrix_finCongr _ hJ

lemma selectedColGramCast_inv_trace {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m) (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGramCast A J hJ)⁻¹).trace =
      ((selectedColGram A J)⁻¹).trace := by
  rw [show (selectedColGramCast A J hJ)⁻¹ =
        (selectedColGram A J)⁻¹.submatrix (finCongr hJ.symm) (finCongr hJ.symm)
      from inv_submatrix_finCongr _ hJ hG]
  exact trace_submatrix_finCongr _ hJ

lemma selectedColGramCast_apply {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m) (p q : Fin m) :
    selectedColGramCast A J hJ p q =
      ∑ i : Fin k, A i (J.orderEmbOfFin hJ p) * A i (J.orderEmbOfFin hJ q) := by
  simp only [selectedColGramCast, selectedColGram, selectedCols,
    Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, id_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [orderEmbOfFin_comp_finCongr, orderEmbOfFin_comp_finCongr]

/-! ### Erase vs `succAbove` on the increasing enumeration -/

lemma erase_card_succ {n m : ℕ} (J : Finset (Fin n))
    (hJ : J.card = m + 1) (p : Fin (m + 1)) :
    (J.erase (J.orderEmbOfFin hJ p)).card = m := by
  rw [card_erase_of_mem (orderEmbOfFin_mem _ _ _), hJ, Nat.add_sub_cancel]

lemma orderEmb_erase_succAbove {n m : ℕ} (J : Finset (Fin n))
    (hJ : J.card = m + 1) (p : Fin (m + 1)) :
    (J.erase (J.orderEmbOfFin hJ p)).orderEmbOfFin (erase_card_succ J hJ p) =
      fun q => J.orderEmbOfFin hJ (p.succAbove q) := by
  refine (orderEmbOfFin_unique (erase_card_succ J hJ p) ?_ ?_).symm
  · intro q
    refine mem_erase.mpr ⟨?_, orderEmbOfFin_mem _ _ _⟩
    exact (J.orderEmbOfFin hJ).injective.ne (Fin.succAbove_ne p q)
  · exact (J.orderEmbOfFin hJ).strictMono.comp (Fin.strictMono_succAbove p)

lemma selectedColGram_erase_eq_minor {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (p : Fin (m + 1)) :
    selectedColGramCast A (J.erase (J.orderEmbOfFin hJ p))
        (erase_card_succ J hJ p) =
      (selectedColGramCast A J hJ).submatrix p.succAbove p.succAbove := by
  apply Matrix.ext
  intro a b
  have hL := selectedColGramCast_apply A (J.erase (J.orderEmbOfFin hJ p))
    (erase_card_succ J hJ p) a b
  have hR := selectedColGramCast_apply A J hJ (p.succAbove a) (p.succAbove b)
  have hord := orderEmb_erase_succAbove J hJ p
  refine hL.trans ?_
  change (∑ i : Fin k,
      A i ((J.erase (J.orderEmbOfFin hJ p)).orderEmbOfFin
        (erase_card_succ J hJ p) a) *
        A i ((J.erase (J.orderEmbOfFin hJ p)).orderEmbOfFin
          (erase_card_succ J hJ p) b)) =
    selectedColGramCast A J hJ (p.succAbove a) (p.succAbove b)
  rw [hord]
  exact hR.symm

/-! ### Cramer diagonal of the selected Gram -/

lemma selectedColGramCast_adjugate_diag {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (p : Fin (m + 1)) :
    Matrix.adjugate (selectedColGramCast A J hJ) p p =
      (selectedColGramCast A (J.erase (J.orderEmbOfFin hJ p))
        (erase_card_succ J hJ p)).det := by
  have hsgn : (-1 : ℝ) ^ (p + p : ℕ) = 1 := by
    rw [← two_mul, pow_mul, neg_one_pow_two, one_pow]
  have hadj :=
    Matrix.adjugate_fin_succ_eq_det_submatrix (selectedColGramCast A J hJ) p p
  refine hadj.trans ?_
  rw [hsgn, one_mul, selectedColGram_erase_eq_minor A J hJ p]

lemma inv_eq_smul_adjugate {t : ℕ}
    (G : Matrix (Fin t) (Fin t) ℝ) (_hG : G.det ≠ 0) :
    G⁻¹ = G.det⁻¹ • Matrix.adjugate G := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

lemma selectedColGramCast_inv_trace_eq_erase_dets {k n m : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hJ : J.card = m + 1) (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGramCast A J hJ)⁻¹).trace =
      (∑ p : Fin (m + 1),
        (selectedColGram A (J.erase (J.orderEmbOfFin hJ p))).det) /
          (selectedColGram A J).det := by
  have hGc : (selectedColGramCast A J hJ).det ≠ 0 := by
    rwa [selectedColGramCast_det]
  have hinv := inv_eq_smul_adjugate (selectedColGramCast A J hJ) hGc
  have htr :
      ((selectedColGramCast A J hJ)⁻¹).trace =
        (selectedColGramCast A J hJ).det⁻¹ *
          (Matrix.adjugate (selectedColGramCast A J hJ)).trace := by
    rw [hinv, Matrix.trace_smul, smul_eq_mul]
  refine htr.trans ?_
  have hdiag :
      (Matrix.adjugate (selectedColGramCast A J hJ)).trace =
        ∑ p : Fin (m + 1),
          (selectedColGram A (J.erase (J.orderEmbOfFin hJ p))).det := by
    change ∑ p : Fin (m + 1),
        Matrix.adjugate (selectedColGramCast A J hJ) p p =
      ∑ p : Fin (m + 1),
        (selectedColGram A (J.erase (J.orderEmbOfFin hJ p))).det
    refine Fintype.sum_congr _ _ fun p => ?_
    exact (selectedColGramCast_adjugate_diag A J hJ p).trans
      (selectedColGramCast_det A _ _)
  rw [hdiag, selectedColGramCast_det, div_eq_inv_mul]

/-! ### Leave-one-out Gram determinants vs residuals -/

lemma selectedCols_rank_eq_card {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    (selectedCols A J).rank = J.card := by
  have : (selectedColGram A J).rank = Fintype.card (Fin J.card) :=
    Matrix.rank_of_det_ne_zero hG
  simpa [selectedColGram, Matrix.rank_transpose_mul_self, Fintype.card_fin]
    using this

lemma selectedColGram_erase_det_ne_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    (J.erase j).card = 0 ∨ (selectedColGram A (J.erase j)).det ≠ 0 := by
  by_cases h0 : (J.erase j).card = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    have hrJ := selectedCols_rank_eq_card A J hG
    have hrange :
        Set.range (selectedCols A J).col =
          insert (A.col j)
            (Set.range (selectedCols A (J.erase j)).col) := by
      rw [range_selectedCols_col, range_selectedCols_col]
      have : (J : Set (Fin n)) = insert j (J.erase j : Set (Fin n)) := by
        rw [← coe_insert, insert_erase hj]
      rw [this, Set.image_insert_eq]
    have hle :
        (selectedCols A J).rank ≤
          (selectedCols A (J.erase j)).rank + 1 := by
      rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols,
        hrange, Submodule.span_insert]
      have hsup :=
        Submodule.finrank_add_le_finrank_add_finrank
          (Submodule.span ℝ ({A.col j} : Set (Fin k → ℝ)))
          (Submodule.span ℝ (Set.range (selectedCols A (J.erase j)).col))
      have hsing :
          Module.finrank ℝ
              (Submodule.span ℝ ({A.col j} : Set (Fin k → ℝ))) ≤ 1 := by
        simpa using
          (finrank_span_le_card ({A.col j} : Set (Fin k → ℝ)))
      exact
        hsup.trans <|
          (Nat.add_le_add_right hsing _).trans_eq (Nat.add_comm _ _)
    have hrE : (selectedCols A (J.erase j)).rank = (J.erase j).card := by
      have hupper : (selectedCols A (J.erase j)).rank ≤ (J.erase j).card :=
        Matrix.rank_le_width _
      have hcard : (J.erase j).card = J.card - 1 := card_erase_of_mem hj
      omega
    have : (selectedColGram A (J.erase j)).rank = (J.erase j).card := by
      rw [selectedColGram, Matrix.rank_transpose_mul_self, hrE]
    exact det_ne_zero_of_rank_eq _ this

lemma residualSq_mul_erase_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A (J.erase j) j *
        (if (J.erase j).card = 0 then (1 : ℝ)
          else (selectedColGram A (J.erase j)).det) =
      (selectedColGram A J).det := by
  have hj' : j ∉ J.erase j := notMem_erase j J
  have hGe := selectedColGram_erase_det_ne_zero A hj hG
  have hmul := residualSq_mul_gram A hj' hGe
  rwa [insert_erase hj] at hmul

lemma residualSq_erase_ne_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A (J.erase j) j ≠ 0 := by
  have h := residualSq_mul_erase_gram A hj hG
  intro hz
  simp [hz] at h
  exact hG h.symm

lemma erase_det_div_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    (selectedColGram A (J.erase j)).det / (selectedColGram A J).det =
      (residualSq A (J.erase j) j)⁻¹ := by
  have hmul := residualSq_mul_erase_gram A hj hG
  by_cases h0 : (J.erase j).card = 0
  · have hG1 : (selectedColGram A (J.erase j)).det = 1 := by
      have hempty : J.erase j = ∅ := card_eq_zero.mp h0
      rw [hempty]
      exact selectedColGram_empty_det A
    simp [h0] at hmul
    rw [hG1, hmul]
    exact (inv_eq_one_div _).symm
  · have hGe : (selectedColGram A (J.erase j)).det ≠ 0 :=
      (selectedColGram_erase_det_ne_zero A hj hG).resolve_left h0
    simp [h0] at hmul
    have : residualSq A (J.erase j) j =
        (selectedColGram A J).det / (selectedColGram A (J.erase j)).det :=
      (eq_div_iff_mul_eq hGe).mpr hmul
    rw [this, inv_div]

/-! ### Inverse-trace identity -/

lemma sum_orderEmb {n : ℕ} (J : Finset (Fin n)) (f : Fin n → ℝ) :
    ∑ j ∈ J, f j = ∑ p : Fin J.card, f (J.orderEmbOfFin rfl p) := by
  have hinj : Set.InjOn (J.orderEmbOfFin rfl) (univ : Finset (Fin J.card)) :=
    fun p _ q _ hpq => (J.orderEmbOfFin rfl).injective hpq
  have himg : image (J.orderEmbOfFin rfl) univ = J :=
    image_orderEmbOfFin_univ J rfl
  have := sum_image (f := f) hinj
  rw [himg] at this
  exact this

/-- Exact inverse-Frobenius identity: the Gram inverse-trace is the sum of
reciprocal leave-one-out residuals.

This is **not** a polynomial inverse-norm bound. -/
theorem selectedColGram_inv_trace_eq_sum_inv_residual {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGram A J)⁻¹).trace =
      ∑ j ∈ J, (residualSq A (J.erase j) j)⁻¹ := by
  by_cases h0 : J.card = 0
  · have hJ : J = ∅ := card_eq_zero.mp h0
    subst hJ
    have htr : ((selectedColGram A (∅ : Finset (Fin n)))⁻¹).trace = 0 := by
      have hcard : (∅ : Finset (Fin n)).card = 0 := card_empty
      rw [← selectedColGramCast_inv_trace A ∅ hcard hG]
      exact Matrix.trace_eq_zero_of_isEmpty _
    simpa using htr
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hsum := selectedColGramCast_inv_trace_eq_erase_dets A J hm hG
    have hcast := selectedColGramCast_inv_trace A J hm hG
    have hdiv :
        (∑ p : Fin (m + 1),
            (selectedColGram A (J.erase (J.orderEmbOfFin hm p))).det) /
              (selectedColGram A J).det =
          ∑ p : Fin (m + 1),
            (residualSq A (J.erase (J.orderEmbOfFin hm p))
              (J.orderEmbOfFin hm p))⁻¹ := by
      rw [sum_div]
      refine Fintype.sum_congr _ _ fun p => ?_
      exact erase_det_div_gram A (orderEmbOfFin_mem _ _ _) hG
    have hrfl :
        ∑ p : Fin (m + 1),
            (residualSq A (J.erase (J.orderEmbOfFin hm p))
              (J.orderEmbOfFin hm p))⁻¹ =
          ∑ p : Fin J.card,
            (residualSq A (J.erase (J.orderEmbOfFin rfl p))
              (J.orderEmbOfFin rfl p))⁻¹ := by
      refine (Fintype.sum_equiv (finCongr hm)
        (fun p : Fin J.card =>
          (residualSq A (J.erase (J.orderEmbOfFin rfl p))
            (J.orderEmbOfFin rfl p))⁻¹)
        (fun p : Fin (m + 1) =>
          (residualSq A (J.erase (J.orderEmbOfFin hm p))
            (J.orderEmbOfFin hm p))⁻¹)
        fun p => ?_).symm
      have hord : J.orderEmbOfFin rfl p =
          J.orderEmbOfFin hm (finCongr hm p) :=
        (orderEmbOfFin_comp_finCongr J hm (finCongr hm p)).symm
      simp [hord]
    have hJsum := sum_orderEmb J (fun j => (residualSq A (J.erase j) j)⁻¹)
    exact hcast.symm.trans (hsum.trans (hdiv.trans (hrfl.trans hJsum.symm)))

/-! ### Adjugate-trace proxy on square blocks -/

lemma cols_mul_transpose_inv_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)}
    (hJ : J.card = k) (hG : (selectedColGram A J).det ≠ 0) :
    ((colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ)⁻¹).trace =
      ((selectedColGram A J)⁻¹).trace := by
  have hre := colsSubmatrix_eq_selectedCols A hJ
  have hBB :
      (colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ =
        selectedColGramCast A J hJ := by
    rw [hre, selectedColGramCast, selectedColGram]
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
      id_eq]
  have hdetB : (colsSubmatrix A J hJ).det ≠ 0 := by
    have hsq :
        ((colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ).det =
          (colsSubmatrix A J hJ).det ^ 2 := by
      rw [Matrix.det_mul, Matrix.det_transpose, sq]
    have hGdet :
        ((colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ).det =
          (selectedColGram A J).det := by
      rw [hBB, selectedColGramCast_det]
    intro hz
    apply hG
    rw [← hGdet, hsq, hz]
    simp
  have hBu : IsUnit (colsSubmatrix A J hJ).det := Ne.isUnit hdetB
  have hBt : IsUnit ((colsSubmatrix A J hJ)ᵀ).det := by
    simpa [Matrix.det_transpose] using hBu
  have hcycle :
      ((colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ)⁻¹).trace =
        (((colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ)⁻¹).trace := by
    set B := colsSubmatrix A J hJ
    have h1 : (B * Bᵀ)⁻¹ = (Bᵀ)⁻¹ * B⁻¹ := by
      apply Matrix.inv_eq_left_inv
      calc ((Bᵀ)⁻¹ * B⁻¹) * (B * Bᵀ)
          = (Bᵀ)⁻¹ * (B⁻¹ * B) * Bᵀ := by simp [Matrix.mul_assoc]
        _ = (Bᵀ)⁻¹ * (1 : Matrix (Fin k) (Fin k) ℝ) * Bᵀ := by
            rw [Matrix.nonsing_inv_mul B hBu]
        _ = (Bᵀ)⁻¹ * Bᵀ := by simp
        _ = 1 := Matrix.nonsing_inv_mul _ hBt
    have h2 : (Bᵀ * B)⁻¹ = B⁻¹ * (Bᵀ)⁻¹ := by
      apply Matrix.inv_eq_left_inv
      calc (B⁻¹ * (Bᵀ)⁻¹) * (Bᵀ * B)
          = B⁻¹ * ((Bᵀ)⁻¹ * Bᵀ) * B := by simp [Matrix.mul_assoc]
        _ = B⁻¹ * (1 : Matrix (Fin k) (Fin k) ℝ) * B := by
            rw [Matrix.nonsing_inv_mul _ hBt]
        _ = B⁻¹ * B := by simp
        _ = 1 := Matrix.nonsing_inv_mul B hBu
    rw [h1, h2, Matrix.trace_mul_comm]
  have hcol :
      (((colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ)⁻¹).trace =
        ((selectedColGram A J)⁻¹).trace := by
    have : ((colsSubmatrix A J hJ)ᵀ * colsSubmatrix A J hJ)⁻¹ =
        (selectedColGramCast A J hJ)⁻¹ := by rw [hBB]
    exact (congrArg Matrix.trace this).trans
      (selectedColGramCast_inv_trace A J hJ hG)
  exact hcycle.trans hcol

/-- On an invertible `k`-set the Milestone D adjugate-trace proxy is
`volumeWeight · tr(G_J⁻¹)`. Not a polynomial bound. -/
theorem invFrobWeight_eq_volumeWeight_mul_inv_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)}
    (hJ : J.card = k) (hG : (selectedColGram A J).det ≠ 0) :
    invFrobWeight A J =
      volumeWeight A J * ((selectedColGram A J)⁻¹).trace := by
  set M := colsSubmatrix A J hJ * (colsSubmatrix A J hJ)ᵀ
  have hadj : volumeWeightedInvGram A J = Matrix.adjugate M :=
    volumeWeightedInvGram_eq A hJ
  have hvolM : volumeWeight A J = M.det := by
    rw [volumeWeight_eq A hJ, Matrix.det_mul, Matrix.det_transpose, sq]
  have hMdet : M.det ≠ 0 := by
    rwa [← hvolM, volumeWeight_eq_selectedColGram_det A hJ]
  have hinv := inv_eq_smul_adjugate M hMdet
  have htr : M.adjugate.trace = M.det * (M⁻¹).trace := by
    have hsmul : (M⁻¹).trace = M.det⁻¹ * M.adjugate.trace := by
      rw [hinv, Matrix.trace_smul, smul_eq_mul]
    calc M.adjugate.trace
        = M.det * (M.det⁻¹ * M.adjugate.trace) := by field_simp [hMdet]
      _ = M.det * (M⁻¹).trace := by rw [hsmul]
  simp only [invFrobWeight]
  rw [hadj, htr, hvolM, cols_mul_transpose_inv_trace A hJ hG, mul_comm]

/-! ### Quadratic-form form of `σ_min ≥ 1/√tr(G⁻¹)` -/

lemma selectedColGram_isSymm {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) :
    (selectedColGram A J)ᵀ = selectedColGram A J := by
  unfold selectedColGram
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

lemma vecEnergy_selectedCols {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (x : Fin J.card → ℝ) :
    vecEnergy (selectedCols A J *ᵥ x) =
      (x ⬝ᵥ (selectedColGram A J *ᵥ x)) := by
  rw [vecEnergy_eq_dot, selectedColGram]
  have hmul :
      ((selectedCols A J)ᵀ * selectedCols A J) *ᵥ x =
        (selectedCols A J)ᵀ *ᵥ (selectedCols A J *ᵥ x) :=
    mulVec_mul_eq _ _ _
  have h1 :
      (x ⬝ᵥ (((selectedCols A J)ᵀ * selectedCols A J) *ᵥ x)) =
        (x ⬝ᵥ ((selectedCols A J)ᵀ *ᵥ (selectedCols A J *ᵥ x))) := by
    rw [hmul]
  have h3 :=
    transpose_mulVec_dot (selectedCols A J) (selectedCols A J *ᵥ x) x
  exact ((h1.trans (dotProduct_comm _ _)).trans h3).symm

lemma gram_inv_is_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    let N := selectedCols A J * (selectedColGram A J)⁻¹
    Nᵀ * N = (selectedColGram A J)⁻¹ := by
  intro N
  have hGG : (selectedColGram A J)⁻¹ * selectedColGram A J = 1 :=
    Matrix.nonsing_inv_mul _ (Ne.isUnit hG)
  have hsym : ((selectedColGram A J)⁻¹)ᵀ = (selectedColGram A J)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, selectedColGram_isSymm]
  calc Nᵀ * N
      = ((selectedColGram A J)⁻¹)ᵀ * (selectedCols A J)ᵀ *
          selectedCols A J * (selectedColGram A J)⁻¹ := by
        simp only [N, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (selectedColGram A J)⁻¹ * selectedColGram A J *
          (selectedColGram A J)⁻¹ := by
        rw [hsym]
        simp only [selectedColGram, Matrix.mul_assoc]
    _ = (selectedColGram A J)⁻¹ := by
        rw [hGG, Matrix.one_mul]

lemma trace_gram_nonneg {k t : ℕ} (N : Matrix (Fin k) (Fin t) ℝ) :
    0 ≤ (Nᵀ * N).trace := by
  change 0 ≤ ∑ i : Fin t, ∑ j : Fin k, N j i * N j i
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_self_nonneg _

lemma vecEnergy_mulVec_le_frob {k t : ℕ}
    (N : Matrix (Fin k) (Fin t) ℝ) (x : Fin t → ℝ) :
    vecEnergy (N *ᵥ x) ≤ (Nᵀ * N).trace * vecEnergy x := by
  have hterm : ∀ i : Fin k,
      (((fun j => N i j) ⬝ᵥ x) ^ 2) ≤
        vecEnergy (fun j => N i j) * vecEnergy x :=
    fun i => energy_cauchy (fun j => N i j) x
  have hsum :
      (∑ i : Fin k, ((fun j => N i j) ⬝ᵥ x) ^ 2) ≤
        (∑ i : Fin k, vecEnergy (fun j => N i j)) * vecEnergy x := by
    have := Finset.sum_le_sum fun i (_ : i ∈ univ) => hterm i
    simpa [Finset.sum_mul] using this
  have hleft : vecEnergy (N *ᵥ x) =
      ∑ i : Fin k, ((fun j => N i j) ⬝ᵥ x) ^ 2 := by
    simp only [vecEnergy, mulVec_sum_eq, dotProduct_eq, pow_two]
  have hfrob : ∑ i : Fin k, vecEnergy (fun j => N i j) = (Nᵀ * N).trace := by
    unfold vecEnergy
    simp_rw [pow_two]
    trans ∑ j : Fin t, ∑ i : Fin k, N i j * N i j
    · exact Finset.sum_comm
    · rfl
  calc vecEnergy (N *ᵥ x)
      = ∑ i : Fin k, ((fun j => N i j) ⬝ᵥ x) ^ 2 := hleft
    _ ≤ (∑ i : Fin k, vecEnergy (fun j => N i j)) * vecEnergy x := hsum
    _ = (Nᵀ * N).trace * vecEnergy x := by rw [hfrob]

lemma selectedColGram_inv_quad_le_trace {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) (x : Fin J.card → ℝ) :
    (x ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ x)) ≤
      ((selectedColGram A J)⁻¹).trace * vecEnergy x := by
  set N := selectedCols A J * (selectedColGram A J)⁻¹
  have hN : Nᵀ * N = (selectedColGram A J)⁻¹ := gram_inv_is_gram A J hG
  have henergy : vecEnergy (N *ᵥ x) =
      (x ⬝ᵥ ((selectedColGram A J)⁻¹ *ᵥ x)) := by
    have hmul : N *ᵥ x =
        selectedCols A J *ᵥ ((selectedColGram A J)⁻¹ *ᵥ x) :=
      mulVec_mul_eq _ _ _
    have := vecEnergy_selectedCols A J ((selectedColGram A J)⁻¹ *ᵥ x)
    have hGid :
        selectedColGram A J *ᵥ ((selectedColGram A J)⁻¹ *ᵥ x) = x := by
      have h1 : selectedColGram A J * (selectedColGram A J)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ (Ne.isUnit hG)
      calc selectedColGram A J *ᵥ ((selectedColGram A J)⁻¹ *ᵥ x)
          = (selectedColGram A J * (selectedColGram A J)⁻¹) *ᵥ x :=
            (mulVec_mul_eq _ _ _).symm
        _ = (1 : Matrix (Fin J.card) (Fin J.card) ℝ) *ᵥ x := by rw [h1]
        _ = x := one_mulVec_eq _
    rw [hmul, this, hGid]
    exact dotProduct_comm _ _
  have hle := vecEnergy_mulVec_le_frob N x
  rwa [henergy, hN] at hle

lemma selectedColGram_inv_trace_nonneg {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) :
    0 ≤ ((selectedColGram A J)⁻¹).trace := by
  have hN := gram_inv_is_gram A J hG
  have := trace_gram_nonneg (selectedCols A J * (selectedColGram A J)⁻¹)
  rwa [hN] at this

/-- Elementary `σ_min` bound from the inverse-Frobenius energy:
`‖x‖² ≤ ‖A_J x‖² · tr(G_J⁻¹)`.

This is `σ_min(A_J) ≥ 1 / √tr(G⁻¹)`. It does **not** claim a joint
`poly(n,k)` bound, and it does **not** claim this is always larger than
`|det A_J|`. -/
theorem selectedCols_energy_mul_inv_trace_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (hG : (selectedColGram A J).det ≠ 0) (x : Fin J.card → ℝ) :
    vecEnergy x ≤
      vecEnergy (selectedCols A J *ᵥ x) *
        ((selectedColGram A J)⁻¹).trace := by
  set B := selectedCols A J
  set G := selectedColGram A J
  set y := G⁻¹ *ᵥ x
  have hGid : G *ᵥ y = x := by
    have h1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hG)
    calc G *ᵥ y
        = (G * G⁻¹) *ᵥ x := (mulVec_mul_eq _ _ _).symm
      _ = (1 : Matrix (Fin J.card) (Fin J.card) ℝ) *ᵥ x := by rw [h1]
      _ = x := one_mulVec_eq _
  have hdot : ((B *ᵥ x) ⬝ᵥ (B *ᵥ y)) = vecEnergy x := by
    have hmul : Bᵀ *ᵥ (B *ᵥ x) = G *ᵥ x := by
      simp only [G, selectedColGram]
      exact (mulVec_mul_eq _ _ _).symm
    have h1 := transpose_mulVec_dot B (B *ᵥ x) y
    have h2 : ((B *ᵥ x) ⬝ᵥ (B *ᵥ y)) = ((G *ᵥ x) ⬝ᵥ y) := by
      have : ((Bᵀ *ᵥ (B *ᵥ x)) ⬝ᵥ y) = ((B *ᵥ x) ⬝ᵥ (B *ᵥ y)) := h1
      simpa [hmul] using this.symm
    have h3 : ((G *ᵥ x) ⬝ᵥ y) = (x ⬝ᵥ (G *ᵥ y)) := by
      have hsym : Gᵀ = G := selectedColGram_isSymm A J
      have := transpose_mulVec_dot G x y
      simpa [hsym, G] using this
    rw [h2, h3, hGid, vecEnergy_eq_dot]
  have hyenergy : vecEnergy (B *ᵥ y) = (x ⬝ᵥ (G⁻¹ *ᵥ x)) := by
    have := vecEnergy_selectedCols A J y
    rw [this, hGid]
    exact dotProduct_comm _ _
  have hCS :
      (vecEnergy x) ^ 2 ≤
        vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) := by
    have := energy_cauchy (B *ᵥ x) (B *ᵥ y)
    simpa [hdot, hyenergy] using this
  have hquad := selectedColGram_inv_quad_le_trace A J hG x
  have hxnn : 0 ≤ vecEnergy x := vecEnergy_nonneg x
  have hTnn := selectedColGram_inv_trace_nonneg A J hG
  have hbnn : 0 ≤ vecEnergy (B *ᵥ x) := vecEnergy_nonneg _
  by_cases hx0 : vecEnergy x = 0
  · simp [hx0]
    exact mul_nonneg hbnn hTnn
  · have hxpos : 0 < vecEnergy x := lt_of_le_of_ne hxnn (Ne.symm hx0)
    have h1 : vecEnergy x * vecEnergy x ≤
        vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) := by
      simpa [pow_two] using hCS
    have h2 : vecEnergy (B *ᵥ x) * (x ⬝ᵥ (G⁻¹ *ᵥ x)) ≤
        vecEnergy (B *ᵥ x) * (G⁻¹.trace * vecEnergy x) :=
      mul_le_mul_of_nonneg_left hquad hbnn
    have h3 : vecEnergy x * vecEnergy x ≤
        (vecEnergy (B *ᵥ x) * G⁻¹.trace) * vecEnergy x := by
      have := h1.trans h2
      linarith
    exact (le_of_mul_le_mul_right h3 hxpos)

/-! ### CPQR specialisation -/

lemma cpqrSet_gram_det_ne_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (selectedColGram A (cpqrSet A)).det ≠ 0 := by
  have hinv := cpqrIterate_invariant A hA k le_rfl
  by_cases hk : k = 0
  · subst hk
    have hempty : cpqrSet A = (∅ : Finset (Fin n)) := rfl
    rw [hempty, selectedColGram_empty_det]
    exact one_ne_zero
  · exact hinv.2 (Nat.pos_of_ne_zero hk)

/-- Inverse-Frobenius energy of the CPQR Gram is the sum of reciprocal
leave-one-out residuals. Not a `poly(n,k)` bound. -/
theorem cpqr_inv_trace_eq_sum_inv_residual {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ((selectedColGram A (cpqrSet A))⁻¹).trace =
      ∑ j ∈ cpqrSet A,
        (residualSq A ((cpqrSet A).erase j) j)⁻¹ :=
  selectedColGram_inv_trace_eq_sum_inv_residual A (cpqrSet A)
    (cpqrSet_gram_det_ne_zero A hA)

lemma cpqr_last_erase_eq_prefix {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 0 < k) :
    (cpqrSet A).erase (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)) =
      cpqrIterate A (k - 1) := by
  have ht : k - 1 < k := Nat.sub_one_lt_of_lt hk
  have hspec := cpqrChosen_spec A hA ht
  have hset : cpqrSet A =
      insert (cpqrChosen A hA (k - 1) ht) (cpqrIterate A (k - 1)) := by
    simpa [cpqrSet, Nat.sub_add_cancel (Nat.succ_le_of_lt hk)] using hspec.2.1
  rw [hset, erase_insert hspec.1]

/-- The last CPQR pivot contributes the last sequential residual to the
leave-one-out sum, hence that one summand is at most `n-k+1`. The other
`k-1` leave-one-out residuals are not controlled here. -/
theorem cpqr_last_leaveOneOut_residual {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hk : 0 < k) :
    residualSq A
        ((cpqrSet A).erase
          (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)))
        (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)) =
      residualSq A (cpqrIterate A (k - 1))
        (cpqrChosen A hA (k - 1) (Nat.sub_one_lt_of_lt hk)) := by
  rw [cpqr_last_erase_eq_prefix A hA hk]

/-- CPQR form of the elementary `σ_min` bound. Not a joint `poly(n,k)`
theorem. -/
theorem cpqr_selected_energy_mul_inv_trace_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
        ((selectedColGram A (cpqrSet A))⁻¹).trace :=
  selectedCols_energy_mul_inv_trace_ge A (cpqrSet A)
    (cpqrSet_gram_det_ne_zero A hA) x

end StructuredColumnSelection
