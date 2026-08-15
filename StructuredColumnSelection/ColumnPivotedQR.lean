import StructuredColumnSelection.CauchyBinet

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

This module defines the algorithm and records small exact runs. It
does **not** claim a polynomial inverse-norm bound.
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

end StructuredColumnSelection
