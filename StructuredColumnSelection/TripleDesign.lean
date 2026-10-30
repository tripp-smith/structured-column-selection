import StructuredColumnSelection.DesignFrame

/-!
# The weighted signed triple design

An explicit tight design `W Wᵀ = 1` in `ℝ^(n+3)` with `4 (n+3)(n+2)(n+1)`
columns, every column of energy `1 / (4 (n+2)(n+1))`, and every pair of
distinct columns at normalized inner product at most `13/14`.

Columns are indexed by `(p, q, r, σ, τ)` with `p : Fin (n+3)`,
`q : Fin (n+2)`, `r : Fin (n+1)`, and two signs. The coordinates
`p`, `p.succAbove q`, `p.succAbove (q.succAbove r)` are distinct, and the
integer column is `e_p + 2σ e_{q'} + 3τ e_{r'}`. Sign sums kill the cross
terms, so the Gram matrix of the rows is `56 (n+2)(n+1)` times the
identity. The coherence bound is an integer argument: the inner product
of two integer columns is an integer of absolute value at most `14`, and
`±14` would force the columns to be equal or opposite.

No adverse frame is built here; the column energy is above the
`1 / wideRepeats` cap of `wide_design_pivots`. This does not close
outcome 1 or outcome 3.
-/

namespace StructuredColumnSelection

open Classical Finset Matrix
open scoped Matrix

/-- `±1` as an integer. -/
def signOf (b : Bool) : ℤ := if b then 1 else -1

lemma signOf_mul_self (b : Bool) : signOf b * signOf b = 1 := by
  cases b <;> simp [signOf]

lemma signOf_injective : Function.Injective signOf := by
  intro a b h
  cases a <;> cases b <;> simp [signOf] at h ⊢

/-- The integer indicator `[x = y]`. -/
def ind {α : Type*} [DecidableEq α] (x y : α) : ℤ := if x = y then 1 else 0

lemma ind_self {α : Type*} [DecidableEq α] (x : α) : ind x x = 1 := by simp [ind]

lemma ind_of_ne {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) : ind x y = 0 := by
  simp [ind, h]

lemma ind_mul_ind {α : Type*} [DecidableEq α] (x x' y : α) :
    ind x y * ind x' y = if x = x' then ind x y else 0 := by
  by_cases hx : x = y <;> by_cases hx' : x' = y
  · subst hx; subst hx'; simp [ind]
  · subst hx
    have hne : x ≠ x' := fun h => hx' h.symm
    simp [ind, hx', hne]
  · subst hx'
    simp [ind, hx]
  · simp [ind, hx, hx']

lemma ind_mul_one_sub {α : Type*} [DecidableEq α] (x y : α) :
    ind x y * (1 - ind x y) = 0 := by
  unfold ind; split_ifs <;> norm_num

/-- Summing an indicator along an injective map counts the preimage. -/
lemma sum_ind_inj {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (x : β) :
    ∑ j, ind x (f j) = if ∃ j, f j = x then 1 else 0 := by
  by_cases hx : ∃ j, f j = x
  · obtain ⟨j₀, hj₀⟩ := hx
    rw [if_pos ⟨j₀, hj₀⟩]
    rw [Finset.sum_eq_single j₀]
    · simp [ind, hj₀]
    · intro j _ hj
      apply ind_of_ne
      intro h
      exact hj (hf (h.symm.trans hj₀.symm))
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro j _
    apply ind_of_ne
    intro h
    exact hx ⟨j, h.symm⟩

lemma sum_ind_id {m : ℕ} (x : Fin m) : ∑ j : Fin m, ind x j = 1 := by
  rw [sum_ind_inj (fun j => j) (fun _ _ h => h) x, if_pos ⟨x, rfl⟩]

lemma sum_ind_succAbove {m : ℕ} (p x : Fin (m + 1)) :
    ∑ j : Fin m, ind x (p.succAbove j) = 1 - ind x p := by
  rw [sum_ind_inj p.succAbove Fin.succAbove_right_injective x]
  by_cases hx : x = p
  · subst hx
    rw [if_neg, ind_self]
    · norm_num
    · rintro ⟨j, hj⟩
      exact Fin.succAbove_ne _ _ hj
  · rw [if_pos (Fin.exists_succAbove_eq hx), ind_of_ne hx]
    norm_num

lemma succAbove_succAbove_injective {m : ℕ} (p : Fin (m + 2)) (q : Fin (m + 1)) :
    Function.Injective (fun r : Fin m => p.succAbove (q.succAbove r)) :=
  Fin.succAbove_right_injective.comp Fin.succAbove_right_injective

lemma exists_succAbove_succAbove_iff {m : ℕ} (p : Fin (m + 2)) (q : Fin (m + 1))
    (x : Fin (m + 2)) :
    (∃ r : Fin m, p.succAbove (q.succAbove r) = x) ↔ x ≠ p ∧ x ≠ p.succAbove q := by
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨Fin.succAbove_ne _ _, ?_⟩
    intro h
    exact Fin.succAbove_ne q r (Fin.succAbove_right_injective h)
  · rintro ⟨hp, hq⟩
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hp
    have hzq : z ≠ q := by
      rintro rfl
      exact hq hz.symm
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hzq
    exact ⟨r, by rw [hr, hz]⟩

lemma sum_ind_succAbove_succAbove {m : ℕ} (p x : Fin (m + 2)) (q : Fin (m + 1)) :
    ∑ r : Fin m, ind x (p.succAbove (q.succAbove r)) =
      (1 - ind x p) * (1 - ind x (p.succAbove q)) := by
  rw [sum_ind_inj _ (succAbove_succAbove_injective p q) x]
  by_cases hp : x = p
  · subst hp
    rw [if_neg, ind_self]
    · norm_num
    · intro h
      exact ((exists_succAbove_succAbove_iff _ _ _).mp h).1 rfl
  · by_cases hq : x = p.succAbove q
    · rw [if_neg, ind_of_ne hp, hq, ind_self]
      · norm_num
      · intro h
        exact ((exists_succAbove_succAbove_iff _ _ _).mp h).2 hq
    · rw [if_pos ((exists_succAbove_succAbove_iff _ _ _).mpr ⟨hp, hq⟩),
        ind_of_ne hp, ind_of_ne hq]
      norm_num

/-! ### Counting lemmas for the row Gram matrix -/

lemma count_p {n : ℕ} (i : Fin (n + 3)) :
    ∑ p : Fin (n + 3), ∑ _q : Fin (n + 2), ∑ _r : Fin (n + 1), ind i p =
      ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_ind_id]
  push_cast
  ring

lemma count_q {n : ℕ} (i : Fin (n + 3)) :
    ∑ p : Fin (n + 3), ∑ q : Fin (n + 2), ∑ _r : Fin (n + 1), ind i (p.succAbove q) =
      ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
  have h1 : ∀ p : Fin (n + 3),
      ∑ q : Fin (n + 2), ∑ _r : Fin (n + 1), ind i (p.succAbove q) =
        ((n + 1 : ℕ) : ℤ) * (1 - ind i p) := by
    intro p
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_ind_succAbove]
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, sum_ind_id]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

lemma count_r {n : ℕ} (i : Fin (n + 3)) :
    ∑ p : Fin (n + 3), ∑ q : Fin (n + 2), ∑ r : Fin (n + 1),
        ind i (p.succAbove (q.succAbove r)) =
      ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
  have h1 : ∀ p : Fin (n + 3),
      ∑ q : Fin (n + 2), ∑ r : Fin (n + 1), ind i (p.succAbove (q.succAbove r)) =
        ((n + 1 : ℕ) : ℤ) * (1 - ind i p) := by
    intro p
    simp_rw [sum_ind_succAbove_succAbove]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, sum_ind_succAbove]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have he := ind_mul_one_sub i p
    push_cast
    linear_combination he
  simp_rw [h1]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, sum_ind_id]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-! ### The integer columns -/

/-- The integer column `e_p + 2σ e_{q'} + 3τ e_{r'}`. -/
def tripleInt {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) (i : Fin (n + 3)) : ℤ :=
  ind i p + 2 * signOf σ * ind i (p.succAbove q) +
    3 * signOf τ * ind i (p.succAbove (q.succAbove r))

/-- Column index type of the triple design. -/
abbrev TripleIndex (n : ℕ) := Fin (n + 3) × Fin (n + 2) × Fin (n + 1) × Bool × Bool

/-- The integer column attached to an index. -/
def tripleCol {n : ℕ} (a : TripleIndex n) : Fin (n + 3) → ℤ :=
  tripleInt a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

lemma tripleInt_at_p {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) : tripleInt p q r σ τ p = 1 := by
  unfold tripleInt
  rw [ind_self, ind_of_ne (Fin.ne_succAbove _ _), ind_of_ne (Fin.ne_succAbove _ _)]
  ring

lemma tripleInt_at_q {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) : tripleInt p q r σ τ (p.succAbove q) = 2 * signOf σ := by
  unfold tripleInt
  rw [ind_of_ne (Fin.succAbove_ne _ _), ind_self, ind_of_ne]
  · ring
  · intro h
    exact Fin.ne_succAbove q r (Fin.succAbove_right_injective h)

lemma tripleInt_at_r {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) : tripleInt p q r σ τ (p.succAbove (q.succAbove r)) = 3 * signOf τ := by
  unfold tripleInt
  rw [ind_of_ne (Fin.succAbove_ne _ _), ind_of_ne, ind_self]
  · ring
  · intro h
    exact Fin.succAbove_ne q r (Fin.succAbove_right_injective h)

lemma tripleInt_at_other {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) {i : Fin (n + 3)} (hp : i ≠ p) (hq : i ≠ p.succAbove q)
    (hr : i ≠ p.succAbove (q.succAbove r)) : tripleInt p q r σ τ i = 0 := by
  unfold tripleInt
  rw [ind_of_ne hp, ind_of_ne hq, ind_of_ne hr]
  ring

/-- Every coordinate of an integer column is `1` at `p`, `±2` at `q'`, `±3` at `r'`,
and `0` elsewhere. -/
lemma tripleInt_cases {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) (i : Fin (n + 3)) :
    (i = p ∧ tripleInt p q r σ τ i = 1) ∨
      (i = p.succAbove q ∧ tripleInt p q r σ τ i = 2 * signOf σ) ∨
      (i = p.succAbove (q.succAbove r) ∧ tripleInt p q r σ τ i = 3 * signOf τ) ∨
      tripleInt p q r σ τ i = 0 := by
  by_cases hp : i = p
  · subst hp; exact Or.inl ⟨rfl, tripleInt_at_p _ _ _ _ _⟩
  by_cases hq : i = p.succAbove q
  · subst hq; exact Or.inr (Or.inl ⟨rfl, tripleInt_at_q _ _ _ _ _⟩)
  by_cases hr : i = p.succAbove (q.succAbove r)
  · subst hr; exact Or.inr (Or.inr (Or.inl ⟨rfl, tripleInt_at_r _ _ _ _ _⟩))
  exact Or.inr (Or.inr (Or.inr (tripleInt_at_other _ _ _ _ _ hp hq hr)))

lemma two_signOf_ne_one (σ : Bool) : 2 * signOf σ ≠ 1 := by cases σ <;> simp [signOf]
lemma three_signOf_ne_one (τ : Bool) : 3 * signOf τ ≠ 1 := by cases τ <;> simp [signOf]
lemma three_signOf_ne_two_signOf (σ τ : Bool) : 3 * signOf τ ≠ 2 * signOf σ := by
  cases σ <;> cases τ <;> simp [signOf]
lemma two_signOf_ne_zero (σ : Bool) : 2 * signOf σ ≠ 0 := by cases σ <;> simp [signOf]
lemma three_signOf_ne_zero (τ : Bool) : 3 * signOf τ ≠ 0 := by cases τ <;> simp [signOf]

/-- No coordinate of an integer column equals `-1`. -/
lemma tripleInt_ne_neg_one {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) (i : Fin (n + 3)) : tripleInt p q r σ τ i ≠ -1 := by
  rcases tripleInt_cases p q r σ τ i with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h <;> rw [h]
  · norm_num
  · cases σ <;> simp [signOf]
  · cases τ <;> simp [signOf]
  · norm_num

/-- A coordinate equal to `1` is the coordinate `p`. -/
lemma tripleInt_eq_one_iff {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) (i : Fin (n + 3)) : tripleInt p q r σ τ i = 1 ↔ i = p := by
  constructor
  · intro h
    rcases tripleInt_cases p q r σ τ i with ⟨hi, _⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | h'
    · exact hi
    · exact absurd (h'.symm.trans h) (two_signOf_ne_one σ)
    · exact absurd (h'.symm.trans h) (three_signOf_ne_one τ)
    · rw [h'] at h; norm_num at h
  · rintro rfl; exact tripleInt_at_p _ _ _ _ _

/-- Distinct indices give distinct integer columns. -/
lemma tripleInt_injective {n : ℕ} {p p' : Fin (n + 3)} {q q' : Fin (n + 2)}
    {r r' : Fin (n + 1)} {σ σ' τ τ' : Bool}
    (h : tripleInt p q r σ τ = tripleInt p' q' r' σ' τ') :
    p = p' ∧ q = q' ∧ r = r' ∧ σ = σ' ∧ τ = τ' := by
  have hp : p = p' := by
    have h1 : tripleInt p' q' r' σ' τ' p = 1 := by rw [← h]; exact tripleInt_at_p _ _ _ _ _
    exact (tripleInt_eq_one_iff _ _ _ _ _ _).mp h1
  subst hp
  have hq : q = q' ∧ σ = σ' := by
    have h2 : tripleInt p q' r' σ' τ' (p.succAbove q) = 2 * signOf σ := by
      rw [← h]; exact tripleInt_at_q _ _ _ _ _
    rcases tripleInt_cases p q' r' σ' τ' (p.succAbove q) with
      ⟨hi, _⟩ | ⟨hi, h'⟩ | ⟨_, h'⟩ | h'
    · exact absurd hi (Fin.succAbove_ne _ _)
    · refine ⟨Fin.succAbove_right_injective hi, ?_⟩
      have := h'.symm.trans h2
      exact signOf_injective (by linarith)
    · exact absurd (h'.symm.trans h2) (three_signOf_ne_two_signOf σ τ')
    · exact absurd (h'.symm.trans h2) (two_signOf_ne_zero σ).symm
  obtain ⟨rfl, rfl⟩ := hq
  have hr : r = r' ∧ τ = τ' := by
    have h3 : tripleInt p q r' σ τ' (p.succAbove (q.succAbove r)) = 3 * signOf τ := by
      rw [← h]; exact tripleInt_at_r _ _ _ _ _
    rcases tripleInt_cases p q r' σ τ' (p.succAbove (q.succAbove r)) with
      ⟨hi, _⟩ | ⟨hi, _⟩ | ⟨hi, h'⟩ | h'
    · exact absurd hi (Fin.succAbove_ne _ _)
    · exact absurd (Fin.succAbove_right_injective hi) (Fin.succAbove_ne _ _)
    · refine ⟨Fin.succAbove_right_injective (Fin.succAbove_right_injective hi), ?_⟩
      have := h'.symm.trans h3
      exact signOf_injective (by linarith)
    · exact absurd (h'.symm.trans h3) (three_signOf_ne_zero τ).symm
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

lemma tripleCol_injective {n : ℕ} : Function.Injective (tripleCol (n := n)) := by
  rintro ⟨p, q, r, σ, τ⟩ ⟨p', q', r', σ', τ'⟩ h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := tripleInt_injective h
  rfl

lemma tripleCol_at_fst {n : ℕ} (a : TripleIndex n) : tripleCol a a.1 = 1 :=
  tripleInt_at_p _ _ _ _ _

/-- The sign sums of a product of two integer columns at two coordinates. -/
lemma sum_signs (a b c a' b' c' : ℤ) :
    ∑ σ : Bool, ∑ τ : Bool,
      (a + 2 * signOf σ * b + 3 * signOf τ * c) *
        (a' + 2 * signOf σ * b' + 3 * signOf τ * c') =
      4 * (a * a' + 4 * (b * b') + 9 * (c * c')) := by
  simp [signOf]
  ring

/-- Row Gram matrix of the integer columns, as a nested sum. -/
lemma tripleInt_gram_nested {n : ℕ} (i i' : Fin (n + 3)) :
    ∑ p : Fin (n + 3), ∑ q : Fin (n + 2), ∑ r : Fin (n + 1), ∑ σ : Bool, ∑ τ : Bool,
        tripleInt p q r σ τ i * tripleInt p q r σ τ i' =
      if i = i' then 56 * (((n : ℤ) + 2) * ((n : ℤ) + 1)) else 0 := by
  simp only [tripleInt]
  simp_rw [sum_signs, ind_mul_ind]
  by_cases hii : i = i'
  · subst hii
    simp only [if_true]
    have hexp : ∀ (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1)),
        (4 : ℤ) * (ind i p + 4 * ind i (p.succAbove q) +
            9 * ind i (p.succAbove (q.succAbove r))) =
          4 * ind i p + 16 * ind i (p.succAbove q) +
            36 * ind i (p.succAbove (q.succAbove r)) := by
      intros; ring
    simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, count_p, count_q, count_r]
    ring
  · simp [hii]

/-- Row Gram matrix of the integer columns: `56 (n+2)(n+1)` times the identity. -/
lemma tripleInt_gram {n : ℕ} (i i' : Fin (n + 3)) :
    ∑ a : TripleIndex n, tripleCol a i * tripleCol a i' =
      if i = i' then 56 * (((n : ℤ) + 2) * ((n : ℤ) + 1)) else 0 := by
  rw [← tripleInt_gram_nested]
  simp only [Fintype.sum_prod_type]
  rfl

/-- Every integer column has squared length `14`. -/
lemma tripleInt_sq_sum {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1))
    (σ τ : Bool) :
    ∑ i, tripleInt p q r σ τ i * tripleInt p q r σ τ i = 14 := by
  simp only [tripleInt]
  have hpq : p ≠ p.succAbove q := Fin.ne_succAbove _ _
  have hpr : p ≠ p.succAbove (q.succAbove r) := Fin.ne_succAbove _ _
  have hqr : p.succAbove q ≠ p.succAbove (q.succAbove r) := by
    intro h
    exact Fin.ne_succAbove q r (Fin.succAbove_right_injective h)
  have hcross : ∀ x y : Fin (n + 3), x ≠ y → ∑ i, ind i x * ind i y = 0 := by
    intro x y hxy
    apply Finset.sum_eq_zero
    intro i _
    unfold ind
    by_cases hx : i = x
    · subst hx; simp [hxy]
    · simp [hx]
  have hdiag : ∀ x : Fin (n + 3), ∑ i, ind i x * ind i x = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [ind]
    · intro i _ hi; simp [ind, hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hexp : ∀ i : Fin (n + 3),
      (ind i p + 2 * signOf σ * ind i (p.succAbove q) +
          3 * signOf τ * ind i (p.succAbove (q.succAbove r))) *
        (ind i p + 2 * signOf σ * ind i (p.succAbove q) +
          3 * signOf τ * ind i (p.succAbove (q.succAbove r))) =
      ind i p * ind i p +
        4 * (signOf σ * signOf σ) * (ind i (p.succAbove q) * ind i (p.succAbove q)) +
        9 * (signOf τ * signOf τ) * (ind i (p.succAbove (q.succAbove r)) *
          ind i (p.succAbove (q.succAbove r))) +
        4 * signOf σ * (ind i p * ind i (p.succAbove q)) +
        6 * signOf τ * (ind i p * ind i (p.succAbove (q.succAbove r))) +
        12 * (signOf σ * signOf τ) *
          (ind i (p.succAbove q) * ind i (p.succAbove (q.succAbove r))) := by
    intro i; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hdiag, hdiag, hdiag,
    hcross _ _ hpq, hcross _ _ hpr, hcross _ _ hqr, signOf_mul_self, signOf_mul_self]
  ring

lemma tripleCol_sq_sum {n : ℕ} (a : TripleIndex n) :
    ∑ i, tripleCol a i * tripleCol a i = 14 :=
  tripleInt_sq_sum _ _ _ _ _

/-- Cauchy–Schwarz for the integer columns: the inner product squares to at most `196`. -/
lemma tripleCol_inner_sq_le {n : ℕ} (a b : TripleIndex n) :
    (∑ i, tripleCol a i * tripleCol b i) ^ 2 ≤ 196 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (tripleCol a) (tripleCol b)
  simp only [pow_two] at h
  rw [tripleCol_sq_sum, tripleCol_sq_sum] at h
  rw [pow_two]
  linarith [h]

/-- Distinct integer columns have inner product at most `13` in absolute value. -/
lemma tripleCol_inner_le {n : ℕ} {a b : TripleIndex n} (hab : a ≠ b) :
    |∑ i, tripleCol a i * tripleCol b i| ≤ 13 := by
  have hsq := tripleCol_inner_sq_le a b
  set S := ∑ i, tripleCol a i * tripleCol b i with hS
  have hS14 : S ≠ 14 := by
    intro h14
    have hzero : ∑ i, (tripleCol a i - tripleCol b i) * (tripleCol a i - tripleCol b i) = 0 := by
      have hexp : ∀ i, (tripleCol a i - tripleCol b i) * (tripleCol a i - tripleCol b i) =
          tripleCol a i * tripleCol a i + tripleCol b i * tripleCol b i -
            2 * (tripleCol a i * tripleCol b i) := fun i => by ring
      simp_rw [hexp]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS,
        tripleCol_sq_sum, tripleCol_sq_sum, h14]
      norm_num
    have heq : tripleCol a = tripleCol b := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_self_nonneg (tripleCol a i - tripleCol b i))).mp hzero i
        (Finset.mem_univ _)
      have := mul_self_eq_zero.mp hi
      linarith
    exact hab (tripleCol_injective heq)
  have hSneg : S ≠ -14 := by
    intro h14
    have hzero : ∑ i, (tripleCol a i + tripleCol b i) * (tripleCol a i + tripleCol b i) = 0 := by
      have hexp : ∀ i, (tripleCol a i + tripleCol b i) * (tripleCol a i + tripleCol b i) =
          tripleCol a i * tripleCol a i + tripleCol b i * tripleCol b i +
            2 * (tripleCol a i * tripleCol b i) := fun i => by ring
      simp_rw [hexp]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← hS,
        tripleCol_sq_sum, tripleCol_sq_sum, h14]
      norm_num
    have hneg : ∀ i, tripleCol b i = -tripleCol a i := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_self_nonneg (tripleCol a i + tripleCol b i))).mp hzero i
        (Finset.mem_univ _)
      have := mul_self_eq_zero.mp hi
      linarith
    have h1 : tripleCol b a.1 = -1 := by
      rw [hneg a.1, tripleCol_at_fst]
    exact tripleInt_ne_neg_one _ _ _ _ _ _ h1
  have hb : S ≤ 14 ∧ -14 ≤ S := by
    constructor <;> nlinarith
  rw [abs_le]
  omega

/-! ### The real design -/

/-- The normalization constant `√(56 (n+2)(n+1))`. -/
noncomputable def tripleNorm (n : ℕ) : ℝ := Real.sqrt (56 * (((n : ℝ) + 2) * ((n : ℝ) + 1)))

lemma tripleNorm_sq (n : ℕ) : tripleNorm n ^ 2 = 56 * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by
  unfold tripleNorm
  rw [Real.sq_sqrt]
  positivity

/-- The real design matrix on the product index type. -/
noncomputable def tripleDesign (n : ℕ) : Matrix (Fin (n + 3)) (TripleIndex n) ℝ :=
  fun i a => (tripleCol a i : ℝ) / tripleNorm n

lemma tripleDesign_inner (n : ℕ) (a b : TripleIndex n) :
    ∑ i, tripleDesign n i a * tripleDesign n i b =
      ((∑ i, tripleCol a i * tripleCol b i : ℤ) : ℝ) / tripleNorm n ^ 2 := by
  simp only [tripleDesign]
  rw [Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_mul, div_mul_div_comm, pow_two]

lemma tripleDesign_gram (n : ℕ) : tripleDesign n * (tripleDesign n)ᵀ = 1 := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tripleDesign, Matrix.one_apply]
  have hgram := tripleInt_gram (n := n) i i'
  have hcast : ∑ a : TripleIndex n, (tripleCol a i : ℝ) / tripleNorm n *
      ((tripleCol a i' : ℝ) / tripleNorm n) =
      ((∑ a : TripleIndex n, tripleCol a i * tripleCol a i' : ℤ) : ℝ) / tripleNorm n ^ 2 := by
    rw [Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Int.cast_mul, div_mul_div_comm, pow_two]
  rw [hcast, hgram, tripleNorm_sq]
  have hpos : (0 : ℝ) < 56 * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by positivity
  split_ifs with h
  · push_cast
    exact div_self hpos.ne'
  · simp

/-- Every column of the design has energy `1 / (4 (n+2)(n+1))`. -/
lemma tripleDesign_col_energy (n : ℕ) (a : TripleIndex n) :
    vecEnergy (fun i => tripleDesign n i a) = 1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1))) := by
  have h := tripleDesign_inner n a a
  rw [tripleCol_sq_sum, tripleNorm_sq] at h
  have hE : vecEnergy (fun i => tripleDesign n i a) =
      ∑ i, tripleDesign n i a * tripleDesign n i a := by
    simp only [vecEnergy, pow_two]
  rw [hE, h]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Distinct columns of the design have normalized inner product at most `13/14`. -/
lemma tripleDesign_coherence (n : ℕ) {a b : TripleIndex n} (hab : a ≠ b) :
    |∑ i, tripleDesign n i a * tripleDesign n i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => tripleDesign n i a)) *
        Real.sqrt (vecEnergy (fun i => tripleDesign n i b))) := by
  have hE : (0 : ℝ) ≤ 1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1))) := by positivity
  rw [tripleDesign_inner, tripleDesign_col_energy, tripleDesign_col_energy,
    ← Real.sqrt_mul hE, ← pow_two, Real.sqrt_sq hE, tripleNorm_sq]
  have hpos : (0 : ℝ) < 56 * (((n : ℝ) + 2) * ((n : ℝ) + 1)) := by positivity
  rw [abs_div, abs_of_pos hpos]
  have hint := tripleCol_inner_le hab
  have hcast : |((∑ i, tripleCol a i * tripleCol b i : ℤ) : ℝ)| ≤ 13 := by
    rw [← Int.cast_abs]
    exact_mod_cast hint
  rw [div_le_iff₀ hpos]
  have hX : ((n : ℝ) + 2) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have hid : 13 / 14 * (1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1)))) *
      (56 * (((n : ℝ) + 2) * ((n : ℝ) + 1))) = 13 := by
    field_simp
    ring
  rw [hid]
  exact hcast

/-- Number of columns of the triple design. -/
def tripleCount (n : ℕ) : ℕ := 4 * ((n + 3) * (n + 2) * (n + 1))

lemma tripleIndex_card (n : ℕ) : Fintype.card (TripleIndex n) = tripleCount n := by
  simp only [TripleIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, tripleCount]
  ring

/-- Reindexing of the column index type by `Fin (tripleCount n)`. -/
noncomputable def tripleEquiv (n : ℕ) : TripleIndex n ≃ Fin (tripleCount n) :=
  (Fintype.equivFin _).trans (finCongr (tripleIndex_card n))

/-- The triple design with columns indexed by `Fin (4 (n+3)(n+2)(n+1))`. -/
noncomputable def tripleDesignFin (n : ℕ) : Matrix (Fin (n + 3)) (Fin (tripleCount n)) ℝ :=
  fun i j => tripleDesign n i ((tripleEquiv n).symm j)

lemma tripleDesignFin_gram (n : ℕ) : tripleDesignFin n * (tripleDesignFin n)ᵀ = 1 := by
  have h := tripleDesign_gram n
  ext i i'
  have hi := congrFun (congrFun h i) i'
  rw [← hi]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tripleDesignFin]
  exact Equiv.sum_comp (tripleEquiv n).symm
    (fun a => tripleDesign n i a * tripleDesign n i' a)

lemma tripleDesignFin_col_energy (n : ℕ) (j : Fin (tripleCount n)) :
    vecEnergy (fun i => tripleDesignFin n i j) =
      1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1))) :=
  tripleDesign_col_energy n _

lemma tripleDesignFin_coherence (n : ℕ) {a b : Fin (tripleCount n)} (hab : a ≠ b) :
    |∑ i, tripleDesignFin n i a * tripleDesignFin n i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => tripleDesignFin n i a)) *
        Real.sqrt (vecEnergy (fun i => tripleDesignFin n i b))) := by
  apply tripleDesign_coherence
  intro h
  exact hab ((tripleEquiv n).symm.injective h)

/-- The weighted signed triple design: a tight design in `ℝ^(n+3)` with
`4 (n+3)(n+2)(n+1)` columns, equal column energy `1 / (4 (n+2)(n+1))`, and
pairwise normalized inner product at most `13/14`. -/
theorem triple_design (n : ℕ) :
    ∃ W : Matrix (Fin (n + 3)) (Fin (4 * ((n + 3) * (n + 2) * (n + 1)))) ℝ,
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) = 1 / (4 * (((n : ℝ) + 2) * ((n : ℝ) + 1)))) ∧
      ∀ a b, a ≠ b →
        |∑ i, W i a * W i b| ≤
          13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
            Real.sqrt (vecEnergy (fun i => W i b))) :=
  ⟨tripleDesignFin n, tripleDesignFin_gram n, tripleDesignFin_col_energy n,
    fun _ _ hab => tripleDesignFin_coherence n hab⟩

end StructuredColumnSelection
