import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.ResidualEnergy
import StructuredColumnSelection.VolumeWeights
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-!
# First-pivot leverage and the k = 1 CPQR volume bound

Empty residuals sum to `k`, so a first CPQR pivot has leverage at
least `k / n`. For a single orthonormal row that is already the
selected volume: `volumeWeight A (cpqrSet A) ≥ n⁻¹`.

The corresponding inverse magnitude is at most `√n`, which matches
the workshop scale `√(k(n-k+1))` when `k = 1`. This does **not**
give a polynomial inverse-norm bound for general `k`.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-- A first CPQR pivot has leverage at least `k / n`. -/
theorem firstLeverage_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {j : Fin n} (hj : cpqrPivot A ∅ = some j) :
    (k : ℝ) / n ≤ residualSq A ∅ j := by
  have hn : 0 < n := by
    simpa [Fintype.card_fin] using
      (Fintype.card_pos_iff.mpr ⟨j⟩ : 0 < Fintype.card (Fin n))
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum := leverageSum A hA
  have hle : ∀ j' : Fin n, residualSq A ∅ j' ≤ residualSq A ∅ j :=
    firstPivot_is_max A hj
  have hbound :
      ∑ j' : Fin n, residualSq A ∅ j' ≤ ∑ _ : Fin n, residualSq A ∅ j :=
    Finset.sum_le_sum fun j' _ => hle j'
  have : (k : ℝ) ≤ n * residualSq A ∅ j := by
    simpa [hsum, Finset.sum_const, nsmul_eq_mul, Fintype.card_fin] using hbound
  exact (div_le_iff₀ hn0).mpr (by rw [mul_comm]; exact this)

lemma volumeWeight_singleton {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (j : Fin n) :
    volumeWeight A {j} = residualSq A ∅ j := by
  have hcard : ({j} : Finset (Fin n)).card = 1 := card_singleton j
  rw [volumeWeight_eq A hcard, residualSq_empty, Matrix.det_fin_one]
  have hentry : colsSubmatrix A {j} hcard 0 0 = A 0 j := by
    simp [colsSubmatrix, Matrix.submatrix_apply]
  rw [hentry]
  have hone : ∑ i : Fin 1, A i j ^ 2 = A 0 j ^ 2 := by
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · intro i _ hi
      exact (hi (Fin.ext (Nat.lt_one_iff.mp i.isLt))).elim
    · intro h
      exact (h (mem_univ 0)).elim
  rw [hone, pow_two]

lemma cpqrSet_eq_singleton_of_k1 {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∃ j : Fin n, cpqrPivot A ∅ = some j ∧ cpqrSet A = {j} := by
  have hcard := cpqrSet_card_eq A hA
  cases h : cpqrPivot A ∅ with
  | none =>
    have : (cpqrSet A).card = 0 := by
      simp [cpqrSet, cpqrIterate, h]
    omega
  | some j =>
    refine ⟨j, rfl, ?_⟩
    simp [cpqrSet, cpqrIterate, h]

/-- For a single orthonormal row, CPQR selects a maximum-magnitude
entry whose squared size is at least `n⁻¹`. -/
theorem cpqr_k1_volume_ge {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (n : ℝ)⁻¹ ≤ volumeWeight A (cpqrSet A) := by
  obtain ⟨j, hj, hJ⟩ := cpqrSet_eq_singleton_of_k1 A hA
  have hlev := firstLeverage_ge A hA hj
  rw [hJ, volumeWeight_singleton, ← one_div]
  simpa using hlev

/-! ## Binomial volume lower bound

The product of CPQR pivot residuals equals `volumeWeight`. Each residual
is at least the complementary-rank average, so the selected volume is at
least `1 / C(n,k)`. That factor is exponential in `k` when `n ≈ 2k` and
is **not** a polynomial inverse-norm bound.
-/

lemma gram_det_reindex {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ)
    (e : Fin t ≃ Fin t) :
    ((B.submatrix id e)ᵀ * B.submatrix id e).det = (Bᵀ * B).det := by
  have h : (B.submatrix id e)ᵀ * B.submatrix id e = (Bᵀ * B).submatrix e e := by
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [h, Matrix.det_submatrix_equiv_self]

lemma gram_det_reindex_equiv {k t s : ℕ} (B : Matrix (Fin k) (Fin t) ℝ)
    (e : Fin s ≃ Fin t) :
    ((B.submatrix id e)ᵀ * B.submatrix id e).det = (Bᵀ * B).det := by
  have h : (B.submatrix id e)ᵀ * B.submatrix id e = (Bᵀ * B).submatrix e e := by
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  rw [h, Matrix.det_submatrix_equiv_self]

/-- Increasing enumeration of `J`, then `j`. -/
def appendEnum {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (p : Fin (J.card + 1)) : Fin n :=
  if h : (p : ℕ) < J.card then J.orderEmbOfFin rfl ⟨p, h⟩ else j

lemma appendEnum_mem {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (p : Fin (J.card + 1)) :
    appendEnum J j p ∈ insert j J := by
  dsimp [appendEnum]
  split_ifs with h
  · exact mem_insert_of_mem (orderEmbOfFin_mem _ _ _)
  · exact mem_insert_self _ _

lemma appendEnum_injective {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ J) :
    Function.Injective (appendEnum J j) := by
  intro p q hpq
  unfold appendEnum at hpq
  by_cases hp : (p : ℕ) < J.card
  · by_cases hq : (q : ℕ) < J.card
    · rw [dif_pos hp, dif_pos hq] at hpq
      have hfin : (⟨p, hp⟩ : Fin J.card) = ⟨q, hq⟩ :=
        (J.orderEmbOfFin rfl).injective hpq
      apply Fin.ext
      exact congrArg (fun x : Fin J.card => (x : ℕ)) hfin
    · rw [dif_pos hp, dif_neg hq] at hpq
      have : j ∈ J := by
        rw [← hpq]
        exact orderEmbOfFin_mem J rfl ⟨p, hp⟩
      exact (hj this).elim
  · by_cases hq : (q : ℕ) < J.card
    · rw [dif_neg hp, dif_pos hq] at hpq
      have : j ∈ J := by
        rw [hpq]
        exact orderEmbOfFin_mem J rfl ⟨q, hq⟩
      exact (hj this).elim
    · apply Fin.ext
      have hp' : (p : ℕ) = J.card :=
        le_antisymm (Nat.lt_succ_iff.mp p.isLt) (le_of_not_gt hp)
      have hq' : (q : ℕ) = J.card :=
        le_antisymm (Nat.lt_succ_iff.mp q.isLt) (le_of_not_gt hq)
      exact hp'.trans hq'.symm

lemma appendEnum_range {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ J) :
    Set.range (appendEnum J j) = insert j (J : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have : appendEnum J j p ∈ insert j J := appendEnum_mem J j p
    rw [← Finset.coe_insert]
    exact this
  · intro hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · refine ⟨Fin.last J.card, ?_⟩
      simp [appendEnum, Fin.last]
    · have : x ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]
        exact hx
      obtain ⟨p, hp⟩ := this
      refine ⟨p.castSucc, ?_⟩
      simp [appendEnum, hp]

lemma appendColumn_eq_submatrix_appendEnum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n) :
    appendColumn (selectedCols A J) (fun i => A i j) =
      A.submatrix id (appendEnum J j) := by
  apply Matrix.ext
  intro i p
  simp only [appendColumn, appendEnum, selectedCols, Matrix.submatrix_apply, id_eq]
  split_ifs <;> rfl

noncomputable def appendToInsertEquiv {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ J) : Fin (J.card + 1) ≃ Fin (insert j J).card :=
  (Equiv.ofInjective (appendEnum J j) (appendEnum_injective J j hj)).trans <|
    (Equiv.setCongr (appendEnum_range J j hj)).trans <|
      (Equiv.setCongr
        ((Finset.range_orderEmbOfFin (insert j J) rfl).trans
          (Finset.coe_insert j J)).symm).trans
        (Equiv.ofInjective ((insert j J).orderEmbOfFin rfl)
          ((insert j J).orderEmbOfFin rfl).injective).symm

lemma appendEnum_eq_orderEmb {n : ℕ} (J : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ J) (p : Fin (J.card + 1)) :
    appendEnum J j p =
      (insert j J).orderEmbOfFin rfl (appendToInsertEquiv J j hj p) := by
  unfold appendToInsertEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply]
  set b :=
    (Equiv.setCongr
        ((Finset.range_orderEmbOfFin (insert j J) rfl).trans
          (Finset.coe_insert j J)).symm)
      ((Equiv.setCongr (appendEnum_range J j hj))
        (Equiv.ofInjective (appendEnum J j) (appendEnum_injective J j hj) p))
  have hord := Equiv.apply_ofInjective_symm
    ((insert j J).orderEmbOfFin rfl).injective b
  exact (rfl : appendEnum J j p = (b : Fin n)).trans hord.symm

lemma appendColumn_eq_selectedCols_insert {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ J) :
    appendColumn (selectedCols A J) (fun i => A i j) =
      (selectedCols A (insert j J)).submatrix id (appendToInsertEquiv J j hj) := by
  apply Matrix.ext
  intro i p
  have h := appendEnum_eq_orderEmb J j hj p
  rw [appendColumn_eq_submatrix_appendEnum]
  simp only [selectedCols, Matrix.submatrix_apply, id_eq, h]

lemma appendColumn_gram_det_eq_insert {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ J) :
    ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
        appendColumn (selectedCols A J) (fun i => A i j)).det =
      (selectedColGram A (insert j J)).det := by
  rw [appendColumn_eq_selectedCols_insert A hj, selectedColGram,
    gram_det_reindex_equiv]

lemma residualSq_mul_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ J)
    (hG : J.card = 0 ∨ (selectedColGram A J).det ≠ 0) :
    residualSq A J j *
        (if J.card = 0 then (1 : ℝ) else (selectedColGram A J).det) =
      (selectedColGram A (insert j J)).det := by
  by_cases h0 : J.card = 0
  · have hJ : J = ∅ := Finset.card_eq_zero.mp h0
    subst hJ
    simp only [h0, ↓reduceIte, mul_one]
    have hsing : insert j (∅ : Finset (Fin n)) = {j} := by simp
    rw [hsing]
    have henergy : residualSq A ∅ j = ∑ i : Fin k, A i j ^ 2 :=
      residualSq_empty A j
    rw [henergy]
    have hgram : selectedColGram A {j} =
        fun p q => ∑ i : Fin k, A i j * A i j := by
      apply Matrix.ext
      intro p q
      simp only [selectedColGram, Matrix.mul_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [selectedCols, Matrix.submatrix_apply, orderEmbOfFin_singleton_apply]
    have e : Fin 1 ≃ Fin ({j} : Finset (Fin n)).card :=
      finCongr (card_singleton j).symm
    let G1 : Matrix (Fin 1) (Fin 1) ℝ :=
      fun _ _ => ∑ i : Fin k, A i j * A i j
    have hre : (selectedColGram A {j}).submatrix e e = G1 := by
      apply Matrix.ext
      intro p q
      change selectedColGram A {j} (e p) (e q) = ∑ i : Fin k, A i j * A i j
      simp only [hgram]
    have hdet1 : G1.det = ∑ i : Fin k, A i j * A i j :=
      Matrix.det_fin_one G1
    have : (selectedColGram A {j}).det = ∑ i : Fin k, A i j ^ 2 := by
      have := Matrix.det_submatrix_equiv_self e (selectedColGram A {j})
      rw [← this, hre, hdet1]
      refine Finset.sum_congr rfl fun i _ => (pow_two _).symm
    exact this.symm
  · have hGdet : (selectedColGram A J).det ≠ 0 := hG.resolve_left h0
    have hres : residualSq A J j =
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det /
          (selectedColGram A J).det := by
      unfold residualSq
      simp [h0, hGdet]
    simp only [h0, ↓reduceIte]
    rw [hres, appendColumn_gram_det_eq_insert A hj,
      div_mul_cancel₀ _ hGdet]

lemma orderEmbOfFin_comp_finCongr {n k : ℕ} (J : Finset (Fin n))
    (h : J.card = k) (i : Fin k) :
    J.orderEmbOfFin rfl (finCongr h.symm i) = J.orderEmbOfFin h i := by
  have hf :
      (fun i : Fin k => J.orderEmbOfFin rfl (finCongr h.symm i)) =
        J.orderEmbOfFin h := by
    refine orderEmbOfFin_unique h ?_ ?_
    · intro i
      exact orderEmbOfFin_mem _ _ _
    · intro i i' hii
      refine (J.orderEmbOfFin rfl).strictMono ?_
      exact (show (finCongr h.symm i : ℕ) < (finCongr h.symm i' : ℕ) by
        simpa [finCongr] using hii)
  exact congrArg (fun f : Fin k → Fin n => f i) hf

lemma colsSubmatrix_eq_selectedCols {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} (h : J.card = k) :
    colsSubmatrix A J h =
      (selectedCols A J).submatrix id (finCongr h.symm) := by
  apply Matrix.ext
  intro i p
  have hord := orderEmbOfFin_comp_finCongr J h p
  simp only [colsSubmatrix, selectedCols, Matrix.submatrix_apply, id_eq, hord]

lemma selectedColGram_empty_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) :
    (selectedColGram A (∅ : Finset (Fin n))).det = 1 :=
  Matrix.det_eq_one_of_card_eq_zero (by
    change Fintype.card (Fin 0) = 0
    exact Fintype.card_fin 0)

lemma volumeWeight_eq_selectedColGram_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} (h : J.card = k) :
    volumeWeight A J = (selectedColGram A J).det := by
  have hvol : volumeWeight A J = (colsSubmatrix A J h).det ^ 2 :=
    volumeWeight_eq A h
  have hre := colsSubmatrix_eq_selectedCols A h
  have hgram :
      (colsSubmatrix A J h)ᵀ * colsSubmatrix A J h =
        (selectedColGram A J).submatrix (finCongr h.symm) (finCongr h.symm) := by
    rw [hre, selectedColGram]
    apply Matrix.ext
    intro p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq]
  have hdet :
      ((colsSubmatrix A J h)ᵀ * colsSubmatrix A J h).det =
        (selectedColGram A J).det := by
    rw [hgram, Matrix.det_submatrix_equiv_self]
  have hsq :
      ((colsSubmatrix A J h)ᵀ * colsSubmatrix A J h).det =
        (colsSubmatrix A J h).det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [hvol, ← hsq, hdet]

lemma cpqrIterate_succ_spec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {t : ℕ} (ht : t < k) :
    ∃ j, cpqrPivot A (cpqrIterate A t) = some j ∧
      j ∉ cpqrIterate A t ∧
      cpqrIterate A (t + 1) = insert j (cpqrIterate A t) ∧
      residualSq A (cpqrIterate A t) j = maxResidual A (cpqrIterate A t) ∧
      0 < residualSq A (cpqrIterate A t) j := by
  have hinv := cpqrIterate_invariant A hA t (le_of_lt ht)
  have hG' : (cpqrIterate A t).card = 0 ∨
      (selectedColGram A (cpqrIterate A t)).det ≠ 0 := by
    cases t with
    | zero => exact Or.inl hinv.1
    | succ _ => exact Or.inr (hinv.2 (Nat.succ_pos _))
  have hpos := unused_residual_pos_of_orthogonal A hA (hinv.1.symm ▸ ht) hG'
  obtain ⟨j, hj⟩ := cpqrPivot_exists_of_pos A hpos
  have hspec := cpqrPivot_spec hj
  refine ⟨j, hj, hspec.1, ?_, hspec.2.1, hspec.2.2⟩
  simp [cpqrIterate, hj]

noncomputable def cpqrChosen {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (t : ℕ) (ht : t < k) : Fin n :=
  (cpqrPivot A (cpqrIterate A t)).get <| by
    obtain ⟨j, hj, _⟩ := cpqrIterate_succ_spec A hA ht
    simp [hj]

lemma cpqrChosen_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {t : ℕ} (ht : t < k) :
    cpqrPivot A (cpqrIterate A t) = some (cpqrChosen A hA t ht) := by
  obtain ⟨j, hj, _⟩ := cpqrIterate_succ_spec A hA ht
  simp [cpqrChosen, hj]

lemma cpqrChosen_spec {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {t : ℕ} (ht : t < k) :
    cpqrChosen A hA t ht ∉ cpqrIterate A t ∧
      cpqrIterate A (t + 1) = insert (cpqrChosen A hA t ht) (cpqrIterate A t) ∧
      residualSq A (cpqrIterate A t) (cpqrChosen A hA t ht) =
        maxResidual A (cpqrIterate A t) ∧
      0 < residualSq A (cpqrIterate A t) (cpqrChosen A hA t ht) := by
  have hj := cpqrChosen_eq A hA ht
  have hspec := cpqrPivot_spec hj
  refine ⟨hspec.1, ?_, hspec.2.1, hspec.2.2⟩
  simp [cpqrIterate, hj]

lemma residual_prod_eq_gram {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (t : ℕ) (ht : t ≤ k) :
    (∏ s : Fin t, residualSq A (cpqrIterate A s)
        (cpqrChosen A hA s (Nat.lt_of_lt_of_le s.isLt ht))) =
      if t = 0 then (1 : ℝ)
      else (selectedColGram A (cpqrIterate A t)).det := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht' : t ≤ k := Nat.le_of_succ_le ht
    have hlt : t < k := Nat.lt_of_succ_le ht
    have hstep := cpqrChosen_spec A hA hlt
    have hinv := cpqrIterate_invariant A hA t ht'
    have hG' : (cpqrIterate A t).card = 0 ∨
        (selectedColGram A (cpqrIterate A t)).det ≠ 0 := by
      cases t with
      | zero => exact Or.inl hinv.1
      | succ _ => exact Or.inr (hinv.2 (Nat.succ_pos _))
    have hmul := residualSq_mul_gram A hstep.1 hG'
    have hprod :
        (∏ s : Fin (t + 1), residualSq A (cpqrIterate A s)
            (cpqrChosen A hA s (Nat.lt_of_lt_of_le s.isLt ht))) =
          (∏ s : Fin t, residualSq A (cpqrIterate A s)
              (cpqrChosen A hA s (Nat.lt_of_lt_of_le s.isLt ht'))) *
            residualSq A (cpqrIterate A t) (cpqrChosen A hA t hlt) := by
      exact Fin.prod_univ_castSucc _
    rw [hprod, ih ht']
    have hne : t + 1 ≠ 0 := Nat.succ_ne_zero t
    simp only [hne, ↓reduceIte]
    rw [mul_comm]
    have hif :
        (if (cpqrIterate A t).card = 0 then (1 : ℝ)
          else (selectedColGram A (cpqrIterate A t)).det) =
          if t = 0 then (1 : ℝ)
          else (selectedColGram A (cpqrIterate A t)).det := by
      by_cases hz : t = 0
      · subst hz
        simp [cpqrIterate]
      · have hpos : (cpqrIterate A t).card ≠ 0 := by
          rw [hinv.1]
          exact hz
        simp [hz, hpos]
    rw [← hif, hstep.2.1]
    exact hmul

lemma volumeWeight_cpqr_eq_residual_prod {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    volumeWeight A (cpqrSet A) =
      ∏ s : Fin k, residualSq A (cpqrIterate A s)
        (cpqrChosen A hA s s.isLt) := by
  have hcard := cpqrSet_card_eq A hA
  have hprod := residual_prod_eq_gram A hA k le_rfl
  by_cases hk : k = 0
  · subst hk
    simp [volumeWeight, cpqrSet, cpqrIterate]
  · rw [hprod, if_neg hk, cpqrSet]
    exact volumeWeight_eq_selectedColGram_det A (by simpa [cpqrSet] using hcard)

lemma cpqr_pivot_residual_ge {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {t : ℕ} (ht : t < k) :
    ((k : ℝ) - t) / ((n : ℝ) - t) ≤
      residualSq A (cpqrIterate A t) (cpqrChosen A hA t ht) := by
  have hkn := orthogonalRows_le A hA
  have hcard : (cpqrIterate A t).card = t :=
    (cpqrIterate_invariant A hA t (le_of_lt ht)).1
  have htn : t < n := lt_of_lt_of_le ht hkn
  have hspec := cpqrChosen_spec A hA ht
  cases t with
  | zero =>
    have hj : cpqrPivot A ∅ = some (cpqrChosen A hA 0 ht) := by
      simpa [cpqrIterate] using cpqrChosen_eq A hA ht
    have hlev := firstLeverage_ge A hA hj
    simpa [cpqrIterate] using hlev
  | succ t =>
    have hG := (cpqrIterate_invariant A hA (t + 1) (le_of_lt ht)).2
      (Nat.succ_pos _)
    have hltn : (cpqrIterate A (t + 1)).card < n := by
      rw [hcard]
      exact htn
    have hge := nextResidual_ge A hA (cpqrIterate A (t + 1)) hG hltn
    have : residualSq A (cpqrIterate A (t + 1)) (cpqrChosen A hA (t + 1) ht) =
        maxResidual A (cpqrIterate A (t + 1)) := hspec.2.2.1
    rw [← this, hcard] at hge
    exact hge

lemma choose_prod_eq {k n : ℕ} (hkn : k ≤ n) :
    (∏ t : Fin k, ((k - (t : ℕ) : ℕ) : ℝ) / ((n - (t : ℕ) : ℕ) : ℝ)) =
      (n.choose k : ℝ)⁻¹ := by
  rw [Finset.prod_div_distrib]
  have hnum : (∏ t : Fin k, ((k - (t : ℕ) : ℕ) : ℝ)) = (k.factorial : ℝ) := by
    rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => k - i) k,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have hden : (∏ t : Fin k, ((n - (t : ℕ) : ℕ) : ℝ)) =
      (n.descFactorial k : ℝ) := by
    rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => n - i) k,
      ← Nat.descFactorial_eq_prod_range]
  rw [hnum, hden]
  have hdesc : (n.descFactorial k : ℝ) =
      (k.factorial : ℝ) * (n.choose k : ℝ) := by
    rw [← Nat.cast_mul, Nat.descFactorial_eq_factorial_mul_choose]
  have hk0 : (k.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hch : (n.choose k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne'
  field_simp [hdesc, hk0, hch]
  exact hdesc.symm

/-- CPQR volume is at least the reciprocal binomial coefficient.

This is exponential in `k` when `n ≈ 2k` (`C(2k,k) ∼ 4^k / √(πk)`)
and is not a polynomial inverse-norm bound. -/
theorem cpqr_volume_ge_binomial {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (n.choose k : ℝ)⁻¹ ≤ volumeWeight A (cpqrSet A) := by
  have hkn := orthogonalRows_le A hA
  rw [volumeWeight_cpqr_eq_residual_prod A hA, ← choose_prod_eq hkn]
  refine Finset.prod_le_prod ?_ ?_
  · intro t _
    refine div_nonneg ?_ ?_
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  · intro t _
    have hbound := cpqr_pivot_residual_ge A hA t.isLt
    have hk : ((k : ℝ) - (t : ℕ)) = ((k - (t : ℕ) : ℕ) : ℝ) :=
      (Nat.cast_sub (le_of_lt t.isLt)).symm
    have hn : ((n : ℝ) - (t : ℕ)) = ((n - (t : ℕ) : ℕ) : ℝ) :=
      (Nat.cast_sub (le_of_lt (lt_of_lt_of_le t.isLt hkn))).symm
    rw [← hk, ← hn]
    exact hbound

end StructuredColumnSelection
