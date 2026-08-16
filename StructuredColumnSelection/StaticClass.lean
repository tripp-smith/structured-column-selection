import StructuredColumnSelection.SigmaMinBounds
import StructuredColumnSelection.ResidualMono
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Static classes with a polynomial CPQR inverse-energy bound (Path 3)

`frame38` is a certified `C = 1` counterexample (not a `poly(n,k)`
disproof). After that witness, SPEC §10 asks for the weakest extra
static hypothesis that still gives a polynomial CPQR bound.

The weakest extra hypothesis used here is purely dimensional: no
geometry is added to `A`. If `min(k, n-k) ≤ d`, the already-proved
binomial volume bound is polynomial in `n` of degree `d`, and the
leave-one-out inverse-trace identity upgrades it to

```text
‖x‖² ≤ k · C(n,k) · ‖A_J x‖² ≤ k · n^d · ‖A_J x‖²
```

on the CPQR set `J`. The class includes matrices with singular
`k`-sets, so the hypothesis is materially weaker than “every `k`-set
is well-conditioned.”

Column incoherence and a leverage floor are recorded as static
predicates. They are narrower than `MinDimLe` (they well-condition
every independent `k`-set) and are not claimed to be weakest.

Non-claims (intentional):

* This is **not** a joint `poly(n,k)` inverse-norm bound for every
  orthogonal-row matrix. Path 1 remains open.
* `frame38` does **not** disprove `poly(n,k)`.
* The unrestricted binomial inverse-energy bound is exponential in
  `k` when `n ≈ 2k` and does **not** close Milestone E.
* Milestone E remains **OPEN**.
* No CSSP / Milestone F statement.
-/

namespace StructuredColumnSelection

open Finset
open scoped Matrix

/-! ### Leave-one-out residuals are at most `1` -/

lemma residualSq_le_col_energy {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) (j : Fin n)
    (hG : (selectedColGram A J).det ≠ 0) :
    residualSq A J j ≤ residualSq A ∅ j := by
  have hres := residualSq_eq_energy A J j hG
  have hle :=
    one_sub_selectedProjector_energy_le A J hG (fun i => A i j)
  have hcol : residualSq A ∅ j =
      ((fun i => A i j) ⬝ᵥ fun i => A i j) := by
    rw [residualSq_empty, dotProduct_eq]
    refine Finset.sum_congr rfl fun i _ => pow_two _
  rw [hres, hcol]
  exact hle

lemma residualSq_le_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (j : Fin n)
    (hG : J.card = 0 ∨ (selectedColGram A J).det ≠ 0) :
    residualSq A J j ≤ 1 := by
  have hcol : residualSq A ∅ j ≤ 1 := by
    rw [residualSq_empty]
    simpa [vecEnergy] using col_energy_le A hA j
  cases hG with
  | inl h0 =>
    have hJ : J = ∅ := card_eq_zero.mp h0
    subst hJ
    exact hcol
  | inr hdet =>
    exact (residualSq_le_col_energy A J j hdet).trans hcol

lemma selectedColGram_det_nonneg {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (J : Finset (Fin n)) :
    0 ≤ (selectedColGram A J).det := by
  simpa [selectedColGram] using det_colGram_nonneg (selectedCols A J)

/-! ### Independent Gram determinants are at most `1` -/

lemma selectedColGram_det_le_one {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    (selectedColGram A J).det ≤ 1 := by
  suffices ∀ m (S : Finset (Fin n)), S.card = m →
      (selectedColGram A S).det ≠ 0 → (selectedColGram A S).det ≤ 1 by
    exact this J.card J rfl hG
  intro m
  induction m with
  | zero =>
    intro S hcard _hG
    have hS : S = ∅ := card_eq_zero.mp hcard
    subst hS
    rw [selectedColGram_empty_det]
  | succ m ih =>
    intro S hcard hGS
    have hne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hne
    have hmul := residualSq_mul_erase_gram A hj hGS
    have hres_le : residualSq A (S.erase j) j ≤ 1 :=
      residualSq_le_one A hA (S.erase j) j
        (selectedColGram_erase_det_ne_zero A hj hGS)
    have hres_nn : 0 ≤ residualSq A (S.erase j) j :=
      residualSq_nonneg A (S.erase j) j
    by_cases h0 : (S.erase j).card = 0
    · simp [h0] at hmul
      linarith
    · have hcard' : (S.erase j).card = m := by
        rw [card_erase_of_mem hj, hcard, Nat.succ_sub_one]
      have hGe : (selectedColGram A (S.erase j)).det ≠ 0 :=
        (selectedColGram_erase_det_ne_zero A hj hGS).resolve_left h0
      have ih' := ih (S.erase j) hcard' hGe
      have hEnn : 0 ≤ (selectedColGram A (S.erase j)).det :=
        selectedColGram_det_nonneg A (S.erase j)
      simp [h0] at hmul
      nlinarith

lemma residualSq_erase_ge_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {J : Finset (Fin n)} {j : Fin n}
    (hj : j ∈ J) (hG : (selectedColGram A J).det ≠ 0) :
    (selectedColGram A J).det ≤ residualSq A (J.erase j) j := by
  have hmul := residualSq_mul_erase_gram A hj hG
  have hres_nn : 0 ≤ residualSq A (J.erase j) j :=
    residualSq_nonneg A (J.erase j) j
  by_cases h0 : (J.erase j).card = 0
  · simp [h0] at hmul
    linarith
  · have hGe : (selectedColGram A (J.erase j)).det ≠ 0 :=
      (selectedColGram_erase_det_ne_zero A hj hG).resolve_left h0
    have hEle : (selectedColGram A (J.erase j)).det ≤ 1 :=
      selectedColGram_det_le_one A hA (J.erase j) hGe
    have hEnn : 0 ≤ (selectedColGram A (J.erase j)).det :=
      selectedColGram_det_nonneg A (J.erase j)
    simp [h0] at hmul
    nlinarith

/-- Inverse-Frobenius energy of an independent Gram is at most
`#J / det(G_J)`. Not a joint `poly(n,k)` bound. -/
theorem selectedColGram_inv_trace_le_card_div_det {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (J : Finset (Fin n)) (hG : (selectedColGram A J).det ≠ 0) :
    ((selectedColGram A J)⁻¹).trace ≤
      (J.card : ℝ) / (selectedColGram A J).det := by
  have hdetpos : 0 < (selectedColGram A J).det :=
    lt_of_le_of_ne (selectedColGram_det_nonneg A J) hG.symm
  rw [selectedColGram_inv_trace_eq_sum_inv_residual A J hG]
  have hterm : ∀ j ∈ J,
      (residualSq A (J.erase j) j)⁻¹ ≤ (selectedColGram A J).det⁻¹ := by
    intro j hj
    exact inv_anti₀ hdetpos (residualSq_erase_ge_det A hA hj hG)
  have hsum :=
    sum_le_sum (s := J) (f := fun j => (residualSq A (J.erase j) j)⁻¹)
      (g := fun _ => (selectedColGram A J).det⁻¹) hterm
  have hcard : ∑ _j ∈ J, (selectedColGram A J).det⁻¹ =
      (J.card : ℝ) * (selectedColGram A J).det⁻¹ := by
    simp [sum_const, nsmul_eq_mul]
  rw [hcard, ← div_eq_mul_inv] at hsum
  exact hsum

/-! ### Binomial inverse-energy bound (exponential; not polynomial) -/

lemma choose_le_pow (n r : ℕ) : (n.choose r : ℝ) ≤ (n : ℝ) ^ r := by
  have hdiv := Nat.choose_le_pow_div (α := ℝ) r n
  have hden : 0 < (r.factorial : ℝ) := Nat.cast_pos.mpr r.factorial_pos
  have hfac : (1 : ℝ) ≤ (r.factorial : ℝ) :=
    Nat.one_le_cast.mpr (Nat.succ_le_of_lt r.factorial_pos)
  have hn : 0 ≤ (n : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg _) r
  have : (n : ℝ) ^ r / (r.factorial : ℝ) ≤ (n : ℝ) ^ r :=
    (div_le_iff₀ hden).mpr (by nlinarith [hn, hfac])
  exact hdiv.trans this

lemma choose_eq_choose_min {k n : ℕ} (hkn : k ≤ n) :
    n.choose k = n.choose (min k (n - k)) := by
  by_cases h : k ≤ n - k
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h), Nat.choose_symm hkn]

lemma choose_le_pow_min {k n : ℕ} (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (n : ℝ) ^ min k (n - k) := by
  rw [choose_eq_choose_min hkn]
  exact choose_le_pow n (min k (n - k))

/-- CPQR inverse energy is at most `k · C(n,k)`.

This is exponential in `k` when `n ≈ 2k` (`C(2k,k) ∼ 4^k / √(πk)`)
and is **not** a joint `poly(n,k)` inverse-norm bound. It does not
close Milestone E. -/
theorem cpqr_inv_energy_le_choose {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n.choose k : ℝ) *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) := by
  have hG := cpqrSet_gram_det_ne_zero A hA
  have hcard := cpqrSet_card_eq A hA
  have hkn := orthogonalRows_le A hA
  have henergy :=
    selectedCols_energy_mul_inv_trace_ge A (cpqrSet A) hG x
  have htr :=
    selectedColGram_inv_trace_le_card_div_det A hA (cpqrSet A) hG
  have hvol : (n.choose k : ℝ)⁻¹ ≤ (selectedColGram A (cpqrSet A)).det := by
    have h := cpqr_volume_ge_binomial A hA
    rwa [volumeWeight_eq_selectedColGram_det A
      (by simpa [cpqrSet] using hcard)] at h
  have hchpos : 0 < (n.choose k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hkn)
  have hdiv : (selectedColGram A (cpqrSet A)).det⁻¹ ≤ (n.choose k : ℝ) := by
    have := inv_anti₀ (inv_pos.mpr hchpos) hvol
    rwa [inv_inv] at this
  have htr' : ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
      (k : ℝ) * (n.choose k : ℝ) := by
    have h1 : ((selectedColGram A (cpqrSet A))⁻¹).trace ≤
        (k : ℝ) / (selectedColGram A (cpqrSet A)).det := by
      simpa [hcard] using htr
    have h2 : (k : ℝ) / (selectedColGram A (cpqrSet A)).det ≤
        (k : ℝ) * (n.choose k : ℝ) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
    exact h1.trans h2
  have hBx : 0 ≤ vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
    vecEnergy_nonneg _
  refine henergy.trans ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left htr' hBx

/-! ### Path 3: complementary-dimension class -/

/-- Extra static hypothesis: the rank or the complementary dimension
is at most `d`. Checkable from the shape of `A` alone. -/
def MinDimLe (k n d : ℕ) : Prop :=
  min k (n - k) ≤ d

/-- On the class `min(k, n-k) ≤ d`, CPQR inverse energy is at most
`k · n^d`.

This is polynomial in `n` of degree `d` (with a linear factor `k`).
It is **not** a `poly(n,k)` theorem for every orthogonal-row matrix:
the hypothesis restricts the shape of `A`. It does not close Path 1. -/
theorem cpqr_inv_energy_le_of_minDim {k n d : ℕ}
    (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    (hd : MinDimLe k n d) (x : Fin (cpqrSet A).card → ℝ) :
    vecEnergy x ≤
      (k : ℝ) * (n : ℝ) ^ d *
        vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) := by
  have hkn := orthogonalRows_le A hA
  have hchoose := cpqr_inv_energy_le_choose A hA x
  have hBx : 0 ≤ vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) :=
    vecEnergy_nonneg _
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  by_cases hk : k = 0
  · subst hk
    have hcard0 : (cpqrSet A).card = 0 := by
      simpa using cpqrSet_card_eq A hA
    have : IsEmpty (Fin (cpqrSet A).card) := by
      rw [hcard0]
      infer_instance
    haveI := this
    simp [vecEnergy]
  · have hn : 1 ≤ n :=
      le_trans (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)) hkn
    have hmin : (n : ℝ) ^ min k (n - k) ≤ (n : ℝ) ^ d :=
      pow_le_pow_right₀ (Nat.one_le_cast.mpr hn) hd
    have hch : (n.choose k : ℝ) ≤ (n : ℝ) ^ d :=
      (choose_le_pow_min hkn).trans hmin
    refine hchoose.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hBx
    exact mul_le_mul_of_nonneg_left hch hk0

/-! ### Narrower static predicates (not the weakest class) -/

/-- Absolute inner product of columns `i` and `j`. -/
def colInner {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ r : Fin k, A r i * A r j

/-- Static incoherence: off-diagonal column inner products are at most `ρ`. -/
def ColumnIncoherent {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j → |colInner A i j| ≤ ρ

/-- Static leverage floor: every column energy is at least `μ`. -/
def LeverageFloor {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (μ : ℝ) : Prop :=
  ∀ j : Fin n, μ ≤ residualSq A ∅ j

end StructuredColumnSelection
