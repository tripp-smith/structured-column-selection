import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.VolumeWeights
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Column-pivoted QR (discovery phase)

Ordinary CPQR on `A : k×n` repeatedly inserts the unused column of
largest residual after projection onto the span of the columns already
chosen. Ties break by the smallest index.

The residual is the Gram-determinant ratio

`det(B'ᵀ B') / det(Bᵀ B)`,

where `B` lists the current columns in increasing order and `B'`
appends the candidate. This is `‖(I-Π) a_j‖₂²` on the independent
locus, and `0` if the current Gram is singular.

This module defines the algorithm and proves the structural facts
needed for a full-rank census: leverage scores sum to `k`, the first
pivot maximises empty residual, and an orthogonal-row matrix yields
exactly `k` columns. It does **not** claim a polynomial inverse-norm
bound.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

variable {R : Type*} [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R]

/-- Append a column to a `k × t` block. -/
def appendColumn {k t : ℕ} (B : Matrix (Fin k) (Fin t) R) (v : Fin k → R) :
    Matrix (Fin k) (Fin (t + 1)) R :=
  fun i j => if h : (j : ℕ) < t then B i ⟨j, h⟩ else v i

/-- Selected columns of `A`, listed by the increasing enumeration of `J`. -/
def selectedCols {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : Matrix (Fin k) (Fin J.card) R :=
  A.submatrix id (J.orderEmbOfFin rfl)

/-- Current column Gram `Bᵀ B`. -/
def selectedColGram {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : Matrix (Fin J.card) (Fin J.card) R :=
  (selectedCols A J)ᵀ * selectedCols A J

/-- Squared residual of column `j` after projecting off `span(A_J)`.
The empty-set case is column energy, avoiding `Fin #∅` versus `Fin 0`. -/
def residualSq {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) (j : Fin n) : R :=
  if _h : J.card = 0 then
    ∑ i, A i j ^ 2
  else
    let Gdet := (selectedColGram A J).det
    if Gdet = 0 then
      0
    else
      let B' := appendColumn (selectedCols A J) (fun i => A i j)
      ((B'ᵀ) * B').det / Gdet

omit [LinearOrder R] [DecidableLE R] in
lemma residualSq_empty {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (j : Fin n) :
    residualSq A ∅ j = ∑ i, A i j ^ 2 :=
  dif_pos card_empty

/-- Unused column indices. -/
def unused {n : ℕ} (J : Finset (Fin n)) : Finset (Fin n) :=
  (univ : Finset (Fin n)) \ J

/-- Largest residual among unused columns, or `0` if none remain. -/
def maxResidual {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : R :=
  if h : (unused J).Nonempty then
    (unused J).sup' h (residualSq A J)
  else
    0

/-- Next CPQR pivot: unused column of maximal residual, then minimal index.
Returns `none` when every unused residual is `≤ 0`. -/
def cpqrPivot {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) : Option (Fin n) :=
  let s := (unused J).filter fun j =>
    residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j
  if h : s.Nonempty then some (s.min' h) else none

omit [DecidableLE R] in
lemma cpqrPivot_not_mem {k n : ℕ} {A : Matrix (Fin k) (Fin n) R}
    {J : Finset (Fin n)} {j : Fin n} (hj : cpqrPivot A J = some j) :
    j ∉ J := by
  simp only [cpqrPivot] at hj
  split_ifs at hj with hs
  · injection hj with hj
    have hmem := min'_mem _ hs
    rw [hj] at hmem
    exact (mem_sdiff.mp (mem_filter.mp hmem).1).2

/-- CPQR after `t` greedy steps. -/
def cpqrIterate {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) : ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 =>
    match cpqrPivot A (cpqrIterate A t) with
    | some j => insert j (cpqrIterate A t)
    | none => cpqrIterate A t

omit [DecidableLE R] in
lemma cpqrIterate_card_le {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) (t : ℕ) :
    (cpqrIterate A t).card ≤ t := by
  induction t with
  | zero => simp [cpqrIterate]
  | succ t ih =>
    simp only [cpqrIterate]
    cases h : cpqrPivot A (cpqrIterate A t) with
    | none => exact ih.trans (Nat.le_succ _)
    | some j =>
      have hj : j ∉ cpqrIterate A t := cpqrPivot_not_mem h
      rw [card_insert_of_notMem hj]
      exact Nat.succ_le_succ ih

/-- Size-`k` CPQR column set (at most `k` columns). -/
def cpqrSet {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) : Finset (Fin n) :=
  cpqrIterate A k

omit [DecidableLE R] in
theorem cpqrSet_card_le {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) :
    (cpqrSet A).card ≤ k :=
  cpqrIterate_card_le A k

/-! ### Structural identities for orthogonal-row CPQR -/

lemma unused_empty {n : ℕ} : unused (∅ : Finset (Fin n)) = (univ : Finset (Fin n)) := by
  simp [unused]

omit [LinearOrder R] [DecidableLE R] in
lemma residualSq_empty_sum {k n : ℕ} (A : Matrix (Fin k) (Fin n) R) :
    ∑ j : Fin n, residualSq A ∅ j = ∑ j : Fin n, ∑ i : Fin k, A i j ^ 2 := by
  refine Finset.sum_congr rfl fun j _ => residualSq_empty A j

lemma sum_sq_eq_trace_mul_transpose {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) :
    ∑ j : Fin n, ∑ i : Fin k, A i j ^ 2 = (A * Aᵀ).trace := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (A * Aᵀ) i i = ∑ j : Fin n, A i j ^ 2 := by
    simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact h.symm

/-- Empty residuals are leverage scores; they sum to `k` when `A Aᵀ = I`. -/
theorem leverageSum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ j : Fin n, residualSq A ∅ j = (k : ℝ) := by
  rw [residualSq_empty_sum, sum_sq_eq_trace_mul_transpose, hA, Matrix.trace_one,
    Fintype.card_fin]

lemma det_colGram_nonneg {k t : ℕ} (B : Matrix (Fin k) (Fin t) ℝ) :
    0 ≤ (Bᵀ * B).det := by
  rw [show Bᵀ * B = Bᵀ * (Bᵀ)ᵀ from (by simp [Matrix.transpose_transpose])]
  rw [← volumeWeights_sum_eq_det_mul_transpose (Bᵀ)]
  refine Finset.sum_nonneg fun J _ => ?_
  unfold volumeWeight
  split_ifs
  · exact sq_nonneg _
  · rfl

lemma residualSq_nonneg {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (j : Fin n) :
    0 ≤ residualSq A J j := by
  unfold residualSq
  by_cases hcard : J.card = 0
  · simp [hcard]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · simp [hcard]
    by_cases hG : (selectedColGram A J).det = 0
    · simp [hG]
    · simp [hG]
      refine div_nonneg ?_ ?_
      · simpa [Matrix.transpose_transpose] using
          det_colGram_nonneg (appendColumn (selectedCols A J) (fun i => A i j))
      · simpa [selectedColGram] using det_colGram_nonneg (selectedCols A J)

lemma residualSq_eq_zero_of_nonpos {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (J : Finset (Fin n)) (j : Fin n) (h : residualSq A J j ≤ 0) :
    residualSq A J j = 0 :=
  le_antisymm h (residualSq_nonneg A J j)

omit [DecidableLE R] in
lemma cpqrPivot_spec {k n : ℕ} {A : Matrix (Fin k) (Fin n) R}
    {J : Finset (Fin n)} {j : Fin n} (hj : cpqrPivot A J = some j) :
    j ∉ J ∧ residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j := by
  have hnot : j ∉ J := cpqrPivot_not_mem hj
  simp only [cpqrPivot] at hj
  split_ifs at hj with hs
  injection hj with hj
  have hmem := min'_mem _ hs
  rw [hj] at hmem
  exact ⟨hnot, (mem_filter.mp hmem).2⟩

omit [DecidableLE R] in
lemma residualSq_le_maxResidual {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    {J : Finset (Fin n)} (hJ : (unused J).Nonempty) {j : Fin n}
    (hj : j ∈ unused J) :
    residualSq A J j ≤ maxResidual A J := by
  simp only [maxResidual, hJ, ↓reduceDIte]
  exact le_sup' (residualSq A J) hj

/-- A successful first pivot maximises empty-set residual. -/
theorem firstPivot_is_max {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    {j : Fin n} (hj : cpqrPivot A ∅ = some j) (j' : Fin n) :
    residualSq A ∅ j' ≤ residualSq A ∅ j := by
  have hspec := cpqrPivot_spec hj
  have hunused : (unused (∅ : Finset (Fin n))).Nonempty := by
    refine ⟨j, ?_⟩
    simp [unused]
  have hj' : j' ∈ unused (∅ : Finset (Fin n)) := by
    simp [unused]
  exact (residualSq_le_maxResidual A hunused hj').trans_eq hspec.2.1.symm

lemma det_ne_zero_of_rank_eq {t : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (h : G.rank = t) : G.det ≠ 0 := by
  have hli : LinearIndependent ℝ G.col := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    simp [Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_cols, h]
  exact (Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col hli))

lemma rank_lt_of_det_eq_zero {t : ℕ} (G : Matrix (Fin t) (Fin t) ℝ)
    (h : G.det = 0) : G.rank < t := by
  by_contra hle
  have : G.rank = t :=
    le_antisymm (Matrix.rank_le_width G) (le_of_not_gt hle)
  exact (det_ne_zero_of_rank_eq G this) h

lemma orthogonalRows_rank {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    A.rank = k := by
  have hrank : (A * Aᵀ).rank = A.rank := by
    simpa [Matrix.transpose_transpose] using Matrix.rank_transpose_mul_self (Aᵀ)
  rw [← hrank, hA, Matrix.rank_one, Fintype.card_fin]

omit [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R] in
lemma appendColumn_castSucc {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) (i : Fin k) (p : Fin t) :
    appendColumn B v i p.castSucc = B i p :=
  dif_pos p.isLt

omit [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R] in
lemma appendColumn_last {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) (i : Fin k) :
    appendColumn B v i (Fin.last t) = v i :=
  dif_neg (lt_irrefl _)

lemma appendColumn_mulVec {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) (c : Fin (t + 1) → R) :
    appendColumn B v *ᵥ c =
      B *ᵥ (fun i => c i.castSucc) + c (Fin.last t) • v := by
  ext i
  simp only [Matrix.mulVec_apply_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [appendColumn_castSucc, appendColumn_last, mul_comm (c (Fin.last t))]

omit [Field R] [DecidableEq R] [LinearOrder R] [DecidableLE R] in
lemma selectedCols_col {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) (p : Fin J.card) :
    (selectedCols A J).col p = A.col (J.orderEmbOfFin rfl p) := by
  ext i
  simp [selectedCols, Matrix.col, Matrix.submatrix_apply, Matrix.transpose_apply]

lemma range_selectedCols_col {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) :
    Set.range (selectedCols A J).col = A.col '' (J : Set (Fin n)) := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨J.orderEmbOfFin rfl p, ?_, (selectedCols_col A J p).symm⟩
    exact Finset.orderEmbOfFin_mem _ _ _
  · rintro ⟨j, hj, rfl⟩
    have : j ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hj
    obtain ⟨p, hp⟩ := this
    exact ⟨p, by rw [selectedCols_col, hp]⟩

lemma orderEmbOfFin_singleton_apply {n : ℕ} (j : Fin n)
    (p : Fin ({j} : Finset (Fin n)).card) :
    ({j} : Finset (Fin n)).orderEmbOfFin rfl p = j :=
  Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ p)

lemma selectedCols_singleton_col {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (j : Fin n) (p : Fin ({j} : Finset (Fin n)).card) :
    (selectedCols A {j}).col p = A.col j := by
  rw [selectedCols_col, orderEmbOfFin_singleton_apply]

lemma selectedColGram_singleton_det_ne_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (j : Fin n)
    (h : 0 < residualSq A ∅ j) :
    (selectedColGram A {j}).det ≠ 0 := by
  have hne : A.col j ≠ 0 := by
    intro hz
    have : residualSq A ∅ j = 0 := by
      rw [residualSq_empty]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : A i j = 0 := by
        simpa [Matrix.col, Matrix.transpose_apply] using congrArg (fun f => f i) hz
      simp [this]
    exact h.ne' this
  have hrange : Set.range (selectedCols A {j}).col = {A.col j} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [selectedCols_singleton_col]
      exact Set.mem_singleton _
    · intro hx
      have hx' : x = A.col j := Set.mem_singleton_iff.mp hx
      have hpos : 0 < ({j} : Finset (Fin n)).card := by
        rw [card_singleton]
        exact Nat.zero_lt_one
      have : Nonempty (Fin ({j} : Finset (Fin n)).card) :=
        Fin.pos_iff_nonempty.mp hpos
      obtain ⟨p⟩ := this
      exact ⟨p, (selectedCols_singleton_col A j p).trans hx'.symm⟩
  have hrank : (selectedCols A {j}).rank = 1 := by
    rw [Matrix.rank_eq_finrank_span_cols, hrange]
    exact finrank_span_singleton hne
  have : (selectedColGram A {j}).rank = ({j} : Finset (Fin n)).card := by
    rw [selectedColGram, Matrix.rank_transpose_mul_self, hrank, card_singleton]
  exact det_ne_zero_of_rank_eq _ this

lemma col_eq_zero_of_residualSq_empty {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {j : Fin n}
    (h : residualSq A ∅ j = 0) :
    A.col j = 0 := by
  have hs : ∑ i : Fin k, A i j ^ 2 = 0 := by
    simpa [residualSq_empty] using h
  have hi : ∀ i ∈ (univ : Finset (Fin k)), A i j ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 hs
  ext i
  have := sq_eq_zero_iff.mp (hi i (mem_univ i))
  simpa [Matrix.col, Matrix.transpose_apply] using this

lemma col_mem_span_of_residualSq_eq_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hG : J.card = 0 ∨ (selectedColGram A J).det ≠ 0)
    (hres : residualSq A J j = 0) :
    A.col j ∈ Submodule.span ℝ (Set.range (selectedCols A J).col) := by
  if h0 : J.card = 0 then
    have : J = ∅ := Finset.card_eq_zero.mp h0
    subst this
    rw [col_eq_zero_of_residualSq_empty A hres]
    exact Submodule.zero_mem _
  else
    have hGdet : (selectedColGram A J).det ≠ 0 :=
      hG.resolve_left h0
    have hres' : residualSq A J j =
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det /
          (selectedColGram A J).det := by
      unfold residualSq
      simp [h0, hGdet]
    have hB'det :
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det = 0 := by
      have hx : residualSq A J j = 0 := hres
      rw [hres'] at hx
      exact (div_eq_zero_iff.mp hx).resolve_right hGdet
    set B := selectedCols A J
    set v : Fin k → ℝ := fun i => A i j
    set B' := appendColumn B v
    have hBrank : B.rank = J.card := by
      have : (Bᵀ * B).rank = Fintype.card (Fin J.card) :=
        Matrix.rank_of_det_ne_zero (by simpa [selectedColGram] using hGdet)
      simpa [Matrix.rank_transpose_mul_self, Fintype.card_fin] using this
    have hB'rank : B'.rank < J.card + 1 := by
      have hG' : (B'ᵀ * B').rank < J.card + 1 :=
        rank_lt_of_det_eq_zero (B'ᵀ * B') hB'det
      simpa [Matrix.rank_transpose_mul_self] using hG'
    have hkerpos :
        0 < Module.finrank ℝ (LinearMap.ker B'.mulVecLin) := by
      have hsum := LinearMap.finrank_range_add_finrank_ker B'.mulVecLin
      have hdom : Module.finrank ℝ (Fin (J.card + 1) → ℝ) = J.card + 1 := by
        simp [Module.finrank_pi, Fintype.card_fin]
      have : B'.rank + Module.finrank ℝ (LinearMap.ker B'.mulVecLin) = J.card + 1 := by
        simpa [Matrix.rank, hdom] using hsum
      omega
    have hnt : Nontrivial (LinearMap.ker B'.mulVecLin) :=
      Module.finrank_pos_iff.mp hkerpos
    obtain ⟨⟨c, hc_ker⟩, hc_ne⟩ := exists_ne (0 : LinearMap.ker B'.mulVecLin)
    have hc0 : c ≠ 0 := fun hc => hc_ne (Subtype.ext hc)
    have hmul : B' *ᵥ c = 0 := LinearMap.mem_ker.mp hc_ker
    have hdep : B *ᵥ (fun i => c i.castSucc) + c (Fin.last J.card) • v = 0 := by
      have := appendColumn_mulVec B v c
      rw [← this, hmul]
    by_cases hlast : c (Fin.last J.card) = 0
    · have hfront : B *ᵥ (fun i => c i.castSucc) = 0 := by
        simpa [hlast] using hdep
      have hkerB : LinearMap.ker B.mulVecLin = ⊥ := by
        have hsum := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        have hdom : Module.finrank ℝ (Fin J.card → ℝ) = J.card := by
          simp [Module.finrank_pi, Fintype.card_fin]
        have hsum' : B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) = J.card := by
          simpa [Matrix.rank, hdom] using hsum
        have : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 0 := by
          omega
        exact Submodule.finrank_eq_zero.mp this
      have hfront0 : (fun i : Fin J.card => c i.castSucc) = 0 := by
        have : (fun i : Fin J.card => c i.castSucc) ∈ LinearMap.ker B.mulVecLin := by
          simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hfront
        simpa [hkerB] using this
      have : c = 0 := by
        ext p
        rcases Fin.eq_castSucc_or_eq_last p with ⟨q, hq⟩ | hp
        · rw [hq]
          exact congrFun hfront0 q
        · rw [hp]
          exact hlast
      exact (hc0 this).elim
    · have hv : v = -((c (Fin.last J.card))⁻¹ • (B *ᵥ fun i => c i.castSucc)) := by
        have h1 : c (Fin.last J.card) • v = -(B *ᵥ fun i => c i.castSucc) :=
          eq_neg_of_add_eq_zero_right hdep
        have h2 : v = (c (Fin.last J.card))⁻¹ • (-(B *ᵥ fun i => c i.castSucc)) := by
          rw [← h1, inv_smul_smul₀ hlast]
        rw [h2, smul_neg]
      have hBspan : B *ᵥ (fun i => c i.castSucc) ∈
          Submodule.span ℝ (Set.range B.col) := by
        rw [← Matrix.range_mulVecLin]
        exact LinearMap.mem_range_self _ _
      have : v ∈ Submodule.span ℝ (Set.range B.col) := by
        rw [hv]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hBspan)
      have hvcol : A.col j = v := by
        ext i
        simp [Matrix.col, Matrix.transpose_apply, v]
      simpa [B, hvcol] using this

lemma rank_le_of_unused_in_span {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n))
    (h : ∀ j ∈ unused J,
        A.col j ∈ Submodule.span ℝ (Set.range (selectedCols A J).col)) :
    A.rank ≤ J.card := by
  have hsub :
      Submodule.span ℝ (Set.range A.col) ≤
        Submodule.span ℝ (Set.range (selectedCols A J).col) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    by_cases hj : j ∈ J
    · exact Submodule.subset_span <|
        (range_selectedCols_col A J).symm ▸ ⟨j, hj, rfl⟩
    · exact h j (mem_sdiff.mpr ⟨mem_univ j, hj⟩)
  rw [Matrix.rank_eq_finrank_span_cols]
  refine (Submodule.finrank_mono hsub).trans ?_
  rw [← Matrix.rank_eq_finrank_span_cols]
  exact Matrix.rank_le_width _

lemma appendColumn_col_castSucc {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) (p : Fin t) :
    (appendColumn B v).col p.castSucc = B.col p := by
  ext i
  simp [Matrix.col, Matrix.transpose_apply, appendColumn_castSucc]

lemma appendColumn_col_last {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) :
    (appendColumn B v).col (Fin.last t) = v := by
  ext i
  simp [Matrix.col, Matrix.transpose_apply, appendColumn_last]

lemma range_appendColumn_col {k t : ℕ} (B : Matrix (Fin k) (Fin t) R)
    (v : Fin k → R) :
    Set.range (appendColumn B v).col = insert v (Set.range B.col) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last p with ⟨q, hq⟩ | hp
    · rw [hq, appendColumn_col_castSucc]
      exact Or.inr ⟨q, rfl⟩
    · rw [hp, appendColumn_col_last]
      exact Or.inl rfl
  · rintro (hx | ⟨p, rfl⟩)
    · exact ⟨Fin.last t, hx ▸ appendColumn_col_last B v⟩
    · exact ⟨p.castSucc, appendColumn_col_castSucc B v p⟩

lemma range_selectedCols_insert {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    {J : Finset (Fin n)} {j : Fin n} :
    Set.range (selectedCols A (insert j J)).col =
      insert (A.col j) (Set.range (selectedCols A J).col) := by
  rw [range_selectedCols_col, range_selectedCols_col, Finset.coe_insert, Set.image_insert_eq]

lemma selectedColGram_insert_det_ne_zero {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ J) (hG : J.card = 0 ∨ (selectedColGram A J).det ≠ 0)
    (hres : 0 < residualSq A J j) :
    (selectedColGram A (insert j J)).det ≠ 0 := by
  if h0 : J.card = 0 then
    have : J = ∅ := Finset.card_eq_zero.mp h0
    subst this
    have hsing : insert j (∅ : Finset (Fin n)) = {j} := by simp
    rw [hsing]
    exact selectedColGram_singleton_det_ne_zero A j hres
  else
    have hGdet : (selectedColGram A J).det ≠ 0 := hG.resolve_left h0
    have hres' : residualSq A J j =
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det /
          (selectedColGram A J).det := by
      unfold residualSq
      simp [h0, hGdet]
    have hB'det :
        ((appendColumn (selectedCols A J) (fun i => A i j))ᵀ *
            appendColumn (selectedCols A J) (fun i => A i j)).det ≠ 0 := by
      intro hz
      have : residualSq A J j = 0 := by
        rw [hres', hz, zero_div]
      exact hres.ne' this
    set B := selectedCols A J
    set v : Fin k → ℝ := fun i => A i j
    set B' := appendColumn B v
    have hB'rank : B'.rank = J.card + 1 := by
      have : (B'ᵀ * B').rank = Fintype.card (Fin (J.card + 1)) :=
        Matrix.rank_of_det_ne_zero hB'det
      simpa [Matrix.rank_transpose_mul_self, Fintype.card_fin] using this
    have hv : A.col j = v := by
      ext i
      simp [Matrix.col, Matrix.transpose_apply, v]
    have hrange :
        Set.range (selectedCols A (insert j J)).col = Set.range B'.col := by
      rw [range_selectedCols_insert, range_appendColumn_col, hv]
    have hinsrank : (selectedCols A (insert j J)).rank = J.card + 1 := by
      rw [Matrix.rank_eq_finrank_span_cols, hrange, ← Matrix.rank_eq_finrank_span_cols, hB'rank]
    have hcard' : (insert j J).card = J.card + 1 :=
      card_insert_of_notMem hj
    have : (selectedColGram A (insert j J)).rank = (insert j J).card := by
      rw [selectedColGram, Matrix.rank_transpose_mul_self, hinsrank, hcard']
    exact det_ne_zero_of_rank_eq _ this

lemma cpqrPivot_exists_of_pos {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    {J : Finset (Fin n)} (h : ∃ j ∈ unused J, 0 < residualSq A J j) :
    ∃ j, cpqrPivot A J = some j := by
  obtain ⟨j0, hj0, hj0pos⟩ := h
  have hne : (unused J).Nonempty := ⟨j0, hj0⟩
  obtain ⟨jmax, hjmax, hjmaxeq⟩ := exists_mem_eq_sup' hne (residualSq A J)
  have hmaxeq : maxResidual A J = residualSq A J jmax := by
    simp [maxResidual, hne, hjmaxeq]
  have hmaxpos : 0 < residualSq A J jmax :=
    lt_of_lt_of_le hj0pos <|
      (residualSq_le_maxResidual A hne hj0).trans_eq hmaxeq
  set s := (unused J).filter fun j =>
    residualSq A J j = maxResidual A J ∧ 0 < residualSq A J j
  have hs : s.Nonempty := by
    refine ⟨jmax, mem_filter.mpr ⟨hjmax, ?_⟩⟩
    exact ⟨hmaxeq.symm, hmaxpos⟩
  refine ⟨s.min' hs, ?_⟩
  simp [cpqrPivot, s, hs]

lemma unused_residual_pos_of_orthogonal {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {J : Finset (Fin n)} (hcard : J.card < k)
    (hG : J.card = 0 ∨ (selectedColGram A J).det ≠ 0) :
    ∃ j ∈ unused J, 0 < residualSq A J j := by
  by_contra hnone
  push Not at hnone
  have hspan : ∀ j ∈ unused J,
      A.col j ∈ Submodule.span ℝ (Set.range (selectedCols A J).col) := by
    intro j hj
    exact col_mem_span_of_residualSq_eq_zero A hG
      (residualSq_eq_zero_of_nonpos A J j (hnone j hj))
  have : A.rank ≤ J.card := rank_le_of_unused_in_span A J hspan
  have : A.rank = k := orthogonalRows_rank A hA
  omega

lemma cpqrIterate_invariant {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∀ t, t ≤ k →
      (cpqrIterate A t).card = t ∧
        (0 < t → (selectedColGram A (cpqrIterate A t)).det ≠ 0) := by
  intro t ht
  induction t with
  | zero => simp [cpqrIterate]
  | succ t ih =>
    have ht' : t ≤ k := Nat.le_of_succ_le ht
    obtain ⟨hcard, hG⟩ := ih ht'
    have htlt : t < k := Nat.lt_of_succ_le ht
    have hG' : (cpqrIterate A t).card = 0 ∨
        (selectedColGram A (cpqrIterate A t)).det ≠ 0 := by
      cases t with
      | zero => exact Or.inl hcard
      | succ _ => exact Or.inr (hG (Nat.succ_pos _))
    have hpos := unused_residual_pos_of_orthogonal A hA (hcard.symm ▸ htlt) hG'
    obtain ⟨j, hj⟩ := cpqrPivot_exists_of_pos A hpos
    have hiter : cpqrIterate A (t + 1) = insert j (cpqrIterate A t) := by
      simp [cpqrIterate, hj]
    have hjnot := (cpqrPivot_spec hj).1
    constructor
    · rw [hiter, card_insert_of_notMem hjnot, hcard]
    · intro _
      rw [hiter]
      exact selectedColGram_insert_det_ne_zero A hjnot hG' (cpqrPivot_spec hj).2.2

/-- Orthogonal-row CPQR returns exactly `k` columns. -/
theorem cpqrSet_card_eq {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    (cpqrSet A).card = k :=
  (cpqrIterate_invariant A hA k le_rfl).1

end StructuredColumnSelection
