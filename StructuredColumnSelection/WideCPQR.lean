import StructuredColumnSelection.ResidualMono
import Mathlib.Analysis.Matrix.Order

/-! Polynomial-width Parseval completion and coordinate-prefix CPQR facts.
These construct actual frames; no adverse-family conclusion is asserted by
completion alone. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

/-- Sum of squares of all matrix entries. -/
def frobEnergy {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin k, ∑ j : Fin n, R i j ^ 2

lemma frobEnergy_nonneg {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) :
    0 ≤ frobEnergy R := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

lemma frobEnergy_eq_trace {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) :
    frobEnergy R = (R * Rᵀ).trace := by
  unfold frobEnergy
  rw [sum_comm]
  exact sum_sq_eq_trace_mul_transpose R

lemma mulVec_energy_le_frob {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ)
    (x : Fin n → ℝ) : vecEnergy (R *ᵥ x) ≤ frobEnergy R * vecEnergy x := by
  calc vecEnergy (R *ᵥ x)
      ≤ ∑ i : Fin k, vecEnergy (fun j => R i j) * vecEnergy x := by
        apply sum_le_sum
        intro i _
        exact energy_cauchy (fun j => R i j) x
    _ = _ := by rw [← sum_mul]; rfl

lemma frobEnergy_transpose {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) :
    frobEnergy Rᵀ = frobEnergy R := by
  unfold frobEnergy
  simp only [Matrix.transpose_apply]
  exact sum_comm

lemma complement_posSemidef {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) : (1 - R * Rᵀ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · change (1 - R * Rᵀ)ᴴ = 1 - R * Rᵀ
    have h1 : Rᴴ = Rᵀ := by ext i j; simp
    have h2 : (Rᵀ)ᴴ = R := by ext i j; simp
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, h1, h2]
  · intro x
    have h := mulVec_energy_le_frob Rᵀ x
    rw [frobEnergy_transpose] at h
    have hle : vecEnergy (Rᵀ *ᵥ x) ≤ vecEnergy x :=
      h.trans (by nlinarith [vecEnergy_nonneg x])
    have hprod : (x ⬝ᵥ ((R * Rᵀ) *ᵥ x)) = vecEnergy (Rᵀ *ᵥ x) := by
      rw [mulVec_mul_eq, vecEnergy_eq_dot]
      exact (transpose_mulVec_dot R x (Rᵀ *ᵥ x)).symm
    simpa only [star_trivial, sub_mulVec_eq, one_mulVec_eq, dotProduct_sub_eq,
      ← vecEnergy_eq_dot, hprod] using sub_nonneg.mpr hle

open scoped MatrixOrder in
lemma exists_gram_completion {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) :
    ∃ C : Matrix (Fin k) (Fin k) ℝ,
      R * Rᵀ + C * Cᵀ = 1 ∧ frobEnergy C ≤ (k : ℝ) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (complement_posSemidef R hR).nonneg
  have hstar : star B = Bᵀ := by ext i j; rfl
  have hBB : Bᵀ * B = 1 - R * Rᵀ := by simpa only [hstar] using hB.symm
  have hC : R * Rᵀ + Bᵀ * (Bᵀ)ᵀ = 1 := by rw [Matrix.transpose_transpose, hBB]; abel
  refine ⟨Bᵀ, hC, ?_⟩
  have htrace := congrArg Matrix.trace hC
  have hE : frobEnergy R + frobEnergy Bᵀ = (k : ℝ) := by
    simpa only [Matrix.trace_add, ← frobEnergy_eq_trace,
      Matrix.trace_one, Fintype.card_fin] using htrace
  linarith [frobEnergy_nonneg R]

/-- Preserve R as the first k columns, then repeat every C column t times. -/
noncomputable def paddedFrame {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ) (t : ℕ) :
    Matrix (Fin k) (Fin (k + k*t)) ℝ :=
  fun i j => Fin.addCases (fun q => R i q)
    (fun q => C i (finProdFinEquiv.symm q).1 / Real.sqrt (t : ℝ)) j

lemma paddedFrame_left {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ) (t : ℕ)
    (i j : Fin k) : paddedFrame R C t i (j.castAdd (k*t)) = R i j := by
  simp [paddedFrame]

lemma paddedFrame_right {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ) (t : ℕ)
    (i : Fin k) (j : Fin (k*t)) :
    paddedFrame R C t i (j.natAdd k) = C i (finProdFinEquiv.symm j).1 / Real.sqrt (t : ℝ) := by
  simp [paddedFrame]

lemma nat_mul_sqrt_quotients (t : ℕ) (ht : 0 < t) (a b : ℝ) :
    (t : ℝ) * (a / Real.sqrt (t : ℝ) * (b / Real.sqrt (t : ℝ))) = a*b := by
  have hpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hne := (Real.sqrt_pos.mpr hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  nth_rewrite 1 [← hsq]
  field_simp [hne]

lemma paddedFrame_mul_transpose {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (t : ℕ) (ht : 0 < t) :
    paddedFrame R C t * (paddedFrame R C t)ᵀ = R * Rᵀ + C * Cᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply]
  rw [Fin.sum_univ_add]
  simp only [paddedFrame_left, paddedFrame_right]
  congr 1
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro q _
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
    nat_mul_sqrt_quotients t ht (C i q) (C j q)

lemma col_energy_le_frob {k n : ℕ} (C : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) :
    vecEnergy (fun i => C i j) ≤ frobEnergy C := by
  exact sum_le_sum fun i _ => single_le_sum (fun _ _ => sq_nonneg _) (mem_univ j)

lemma paddedFrame_right_energy_le {k : ℕ} (R C : Matrix (Fin k) (Fin k) ℝ)
    (t : ℕ) (ht : 0 < t) (hC : frobEnergy C ≤ (k : ℝ)) (j : Fin (k*t)) :
    vecEnergy (fun i => paddedFrame R C t i (j.natAdd k)) ≤ (k : ℝ) / t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hcol := (col_energy_le_frob C (finProdFinEquiv.symm j).1).trans hC
  calc vecEnergy (fun i => paddedFrame R C t i (j.natAdd k))
      = vecEnergy (fun i => C i (finProdFinEquiv.symm j).1) / (t : ℝ) := by
        simp only [vecEnergy, paddedFrame_right, div_pow, Real.sq_sqrt htR.le, sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right hcol htR.le

/-- Actual finite Parseval completion, with explicit size and column-energy bound. -/
theorem wide_completion_orthogonal {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) (t : ℕ) (ht : 0 < t) :
    ∃ A : Matrix (Fin k) (Fin (k+k*t)) ℝ, OrthogonalRows A ∧
      (∀ i j : Fin k, A i (j.castAdd (k*t)) = R i j) ∧
      ∀ j : Fin (k*t), vecEnergy (fun i => A i (j.natAdd k)) ≤ (k : ℝ) / t := by
  obtain ⟨C, hCC, hC⟩ := exists_gram_completion R hR
  refine ⟨paddedFrame R C t, ?_, paddedFrame_left R C t, ?_⟩
  · exact (paddedFrame_mul_transpose R C t ht).trans hCC
  · exact paddedFrame_right_energy_le R C t ht hC

/-- The repeated filler block contains two equal columns of positive energy
whenever the leading block does not already fill the identity. -/
theorem wide_completion_with_repeat {k : ℕ} (R : Matrix (Fin k) (Fin k) ℝ)
    (hR : frobEnergy R ≤ 1) (t : ℕ) (ht : 2 ≤ t) (hk : 2 ≤ k) :
    ∃ A : Matrix (Fin k) (Fin (k + k * t)) ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin k, A i (j.castAdd (k * t)) = R i j) ∧
      (∀ j : Fin (k * t),
        vecEnergy (fun i => A i (j.natAdd k)) ≤ (k : ℝ) / t) ∧
      ∃ j1 j2 : Fin (k + k * t),
        j1 ≠ j2 ∧ (∀ i, A i j1 = A i j2) ∧
          0 < vecEnergy (fun i => A i j1) := by
  have ht0 : 0 < t := by omega
  obtain ⟨C, hCC, hCbound⟩ := exists_gram_completion R hR
  have htrace : frobEnergy R + frobEnergy C = (k : ℝ) := by
    have htr := congrArg Matrix.trace hCC
    simpa [Matrix.trace_add, ← frobEnergy_eq_trace, Matrix.trace_one,
      Fintype.card_fin] using htr
  have hCpos : 0 < frobEnergy C := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hsum : frobEnergy C = ∑ j, vecEnergy (fun i => C i j) := by
    unfold frobEnergy vecEnergy
    exact sum_comm
  have hqpos : ∃ q : Fin k, 0 < vecEnergy (fun i => C i q) := by
    by_contra hnone
    push Not at hnone
    have : frobEnergy C ≤ 0 := by
      rw [hsum]
      exact Finset.sum_nonpos fun j _ => hnone j
    linarith
  obtain ⟨q, hq⟩ := hqpos
  let s0 : Fin t := ⟨0, by omega⟩
  let s1 : Fin t := ⟨1, by omega⟩
  let p0 : Fin (k * t) := finProdFinEquiv (q, s0)
  let p1 : Fin (k * t) := finProdFinEquiv (q, s1)
  have hp : p0 ≠ p1 := by
    intro h
    have := finProdFinEquiv.injective h
    simp [s0, s1] at this
  let j1 : Fin (k + k * t) := p0.natAdd k
  let j2 : Fin (k + k * t) := p1.natAdd k
  have hj : j1 ≠ j2 := by
    intro h
    exact hp ((Fin.natAdd_inj k).mp h)
  have hsame : ∀ i, paddedFrame R C t i j1 = paddedFrame R C t i j2 := by
    intro i
    simp [j1, j2, p0, p1, s0, s1, paddedFrame_right]
  have henergy : vecEnergy (fun i => paddedFrame R C t i j1) =
      vecEnergy (fun i => C i q) / (t : ℝ) := by
    have htR : (0 : ℝ) ≤ t := by exact_mod_cast ht0.le
    simp only [vecEnergy, j1, p0, paddedFrame_right, div_pow, Real.sq_sqrt htR, sum_div]
    simp [s0]
  refine ⟨paddedFrame R C t, ?_, paddedFrame_left R C t,
      paddedFrame_right_energy_le R C t ht0 hCbound, ?_⟩
  · exact (paddedFrame_mul_transpose R C t ht0).trans hCC
  · exact ⟨j1, j2, hj, hsame, by
      rw [henergy]
      exact div_pos hq (by exact_mod_cast ht0)⟩

/-- The first t column labels, with no hidden pivot criterion. -/
def widePrefix (n t : ℕ) : Finset (Fin n) := univ.filter fun j => (j : ℕ) < t

/-- Coordinate truncation onto the first t rows. -/
def prefixCut {k : ℕ} (t : ℕ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if (i : ℕ) < t then x i else 0

/-- Exact tail-coordinate energy. -/
def tailEnergy {k : ℕ} (t : ℕ) (x : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, if t ≤ (i : ℕ) then x i ^ 2 else 0

lemma widePrefix_zero (n : ℕ) : widePrefix n 0 = ∅ := by simp [widePrefix]

lemma widePrefix_succ {n : ℕ} (p : Fin n) :
    widePrefix n ((p : ℕ)+1) = insert p (widePrefix n p) := by
  ext j
  simp only [widePrefix, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

lemma leading_prefix_projector {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0) :
    ∀ t ≤ k, (selectedColGram A (widePrefix n t)).det ≠ 0 ∧
      ∀ x, selectedProjector A (widePrefix n t) *ᵥ x = prefixCut t x := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [widePrefix_zero]
    refine ⟨?_, ?_⟩
    · rw [selectedColGram_empty_det]
      norm_num
    · intro x
      rw [selectedProjector_empty]
      ext i
      simp [prefixCut]
  | succ t ih =>
    intro ht
    obtain ⟨hG,hP⟩ := ih (by omega)
    let p : Fin k := ⟨t,by omega⟩
    let q : Fin n := Fin.castLE hkn p
    let a : ℝ := A p q
    let w : Fin k → ℝ := fun i => if i=p then a else 0
    have hnot : q ∉ widePrefix n t := by simp [widePrefix,q,p]
    have ha : a ≠ 0 := hdiag p
    have hw : residualVec A (widePrefix n t) q = w := by
      rw [residualVec_sub, hP]
      ext i
      by_cases hi : i=p
      · subst i
        simp [prefixCut,w,p,a]
      · have hine : (i : ℕ) ≠ t := by intro hh; exact hi (Fin.ext hh)
        by_cases hit : (i : ℕ) < t
        · simp [prefixCut,w,hi,hit]
        · have hti : (p : ℕ) < (i : ℕ) := by dsimp [p]; omega
          have hz := hupper i p hti
          simp [prefixCut,w,hi,hit,q,hz]
    have hδ : residualSq A (widePrefix n t) q = a^2 := by
      rw [← residualVec_sq A _ q hG, hw]
      simp [w,dotProduct,pow_two]
    have hG' : (selectedColGram A (insert q (widePrefix n t))).det ≠ 0 :=
      selectedColGram_insert_det_ne_zero A hnot (Or.inr hG) (by rw [hδ]; exact sq_pos_of_ne_zero ha)
    have hsets : widePrefix n (t+1) = insert q (widePrefix n t) := widePrefix_succ q
    rw [hsets]
    refine ⟨hG', ?_⟩
    intro x
    rw [selectedProjector_insert_mulVec A hnot hG hG', hw, hδ, hP]
    have hdot : x ⬝ᵥ w = x p * a := by simp [w,dotProduct]
    rw [hdot]
    ext i
    by_cases hi : i=p
    · subst i
      simp only [prefixCut, Pi.add_apply, Pi.smul_apply, smul_eq_mul, w]
      simp only [show ¬ (p : ℕ) < t from by dsimp [p]; omega,
        show (p : ℕ) < t+1 from by dsimp [p]; omega, if_false, if_true, zero_add]
      field_simp [ha]
    · have hine : (i : ℕ) ≠ t := by intro hh; exact hi (Fin.ext hh)
      have heq : ((i : ℕ) < t) ↔ ((i : ℕ) < t+1) := by omega
      simp [prefixCut,w,hi,heq]

lemma residualSq_leading_tail {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (t : ℕ) (ht : t ≤ k) (j : Fin n) :
    residualSq A (widePrefix n t) j = tailEnergy t (A.col j) := by
  obtain ⟨hG,hP⟩ := leading_prefix_projector hkn A hupper hdiag t ht
  rw [residualSq_eq_quadForm A _ j hG, sub_mulVec_eq, one_mulVec_eq, hP]
  simp only [dotProduct_eq, Pi.sub_apply, prefixCut, tailEnergy]
  apply sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) < t
  · simp [hi,show ¬ t ≤ (i : ℕ) by omega]
  · simp [hi,show t ≤ (i : ℕ) by omega,pow_two]

lemma leading_tail_diag {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (p : Fin k) :
    tailEnergy p (A.col (Fin.castLE hkn p)) = A p (Fin.castLE hkn p)^2 := by
  unfold tailEnergy
  rw [sum_eq_single p]
  · simp
  · intro i _ hi
    by_cases hpi : (p : ℕ) ≤ (i : ℕ)
    · have hpilt : (p : ℕ) < (i : ℕ) := by
        have : (i : ℕ) ≠ (p : ℕ) := fun h => hi (Fin.ext h)
        omega
      simp [hpi,hupper i p hpilt]
    · simp [hpi]
  · simp

/-- Entry/tail-energy hypotheses imply the actual greedy prefix sequence. -/
theorem triangular_prefix_pivots {k n : ℕ} (hkn : k ≤ n)
    (A : Matrix (Fin k) (Fin n) ℝ)
    (hupper : ∀ i j : Fin k, (j : ℕ) < (i : ℕ) → A i (Fin.castLE hkn j) = 0)
    (hdiag : ∀ i : Fin k, A i (Fin.castLE hkn i) ≠ 0)
    (htail : ∀ p : Fin k, ∀ j : Fin n, (p : ℕ) < (j : ℕ) →
      tailEnergy p (A.col j) < A p (Fin.castLE hkn p)^2) :
    ∀ t ≤ k, cpqrIterate A t = widePrefix n t := by
  have hpivot : ∀ p : Fin k, cpqrPivot A (widePrefix n p) = some (Fin.castLE hkn p) := by
    intro p
    let q := Fin.castLE hkn p
    have hnot : q ∈ unused (widePrefix n p) := by simp [unused,widePrefix,q]
    have hres : residualSq A (widePrefix n p) q = A p q ^ 2 :=
      (residualSq_leading_tail hkn A hupper hdiag p (Nat.le_of_lt p.isLt) q).trans
        (leading_tail_diag hkn A hupper p)
    obtain ⟨j,hj⟩ := cpqrPivot_exists_of_pos A ⟨q,hnot,by rw [hres]; exact sq_pos_of_ne_zero (hdiag p)⟩
    have hspec := cpqrPivot_spec hj
    have hqle := residualSq_le_maxResidual A ⟨q,hnot⟩ hnot
    have heq : j=q := by
      by_contra hne
      have hvalne : (j : ℕ) ≠ (p : ℕ) := fun h => hne (Fin.ext h)
      have hjval : (p : ℕ) < (j : ℕ) := by
        have hnotj := hspec.1
        simp only [widePrefix,mem_filter,mem_univ,true_and] at hnotj
        omega
      have hstrict := htail p j hjval
      rw [← residualSq_leading_tail hkn A hupper hdiag p (Nat.le_of_lt p.isLt) j] at hstrict
      rw [← hres] at hstrict
      linarith [hspec.2.1]
    simpa [heq] using hj
  intro t
  induction t with
  | zero => intro _; simp [cpqrIterate,widePrefix_zero]
  | succ t ih =>
    intro ht
    have htk : t < k := by omega
    rw [cpqrIterate,ih (by omega),hpivot ⟨t,htk⟩]
    exact (widePrefix_succ (Fin.castLE hkn ⟨t,htk⟩)).symm

end StructuredColumnSelection
