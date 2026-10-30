import StructuredColumnSelection.ScaledDesignFrame

/-!
# Filler-pair coherence of the scaled triple-design frame

The frame of `scaled_triple_frame` is `[3 R₀ | C W]`. This file turns the
completion identities and the three-coordinate support of a triple-design
column into normalized coherence bounds for filler–filler pairs and for
leading–filler pairs.

Leading–leading pairs are not bounded here. No coherence bound on the whole
frame is claimed. Outcome 3 stays open.
-/

namespace StructuredColumnSelection

open Classical Finset
open scoped Matrix

/-! ### Completion perturbation of an inner product -/

/-- The completion error `|⟨C w, C v⟩ - ⟨w, v⟩|` is at most
`ε √(‖w‖²) √(‖v‖²)` whenever `‖R‖_F² ≤ ε` and `C` obeys the inner-product
identity. -/
lemma completion_inner_perturb {k : ℕ} (eps : ℝ) (R C : Matrix (Fin k) (Fin k) ℝ)
    (hinner : ∀ w v : Fin k → ℝ,
      (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - (Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v))
    (hR : frobEnergy R ≤ eps) (w v : Fin k → ℝ) :
    |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| ≤
      eps * Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v) := by
  have hε : 0 ≤ eps := (frobEnergy_nonneg R).trans hR
  have hdiff : (C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v =
      -((Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v)) := by
    rw [hinner w v]
    ring
  rw [hdiff, abs_neg]
  have hcs := energy_cauchy (Rᵀ *ᵥ w) (Rᵀ *ᵥ v)
  have hEw : vecEnergy (Rᵀ *ᵥ w) ≤ eps * vecEnergy w := by
    have h := mulVec_energy_le_frob Rᵀ w
    rw [frobEnergy_transpose] at h
    exact h.trans (mul_le_mul_of_nonneg_right hR (vecEnergy_nonneg w))
  have hEv : vecEnergy (Rᵀ *ᵥ v) ≤ eps * vecEnergy v := by
    have h := mulVec_energy_le_frob Rᵀ v
    rw [frobEnergy_transpose] at h
    exact h.trans (mul_le_mul_of_nonneg_right hR (vecEnergy_nonneg v))
  calc |(Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v)|
      = Real.sqrt (((Rᵀ *ᵥ w) ⬝ᵥ (Rᵀ *ᵥ v)) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (vecEnergy (Rᵀ *ᵥ w) * vecEnergy (Rᵀ *ᵥ v)) := Real.sqrt_le_sqrt hcs
    _ ≤ Real.sqrt ((eps * vecEnergy w) * (eps * vecEnergy v)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul hEw hEv (vecEnergy_nonneg _) (mul_nonneg hε (vecEnergy_nonneg _))
    _ = Real.sqrt (eps * vecEnergy w) * Real.sqrt (eps * vecEnergy v) := by
        rw [Real.sqrt_mul (mul_nonneg hε (vecEnergy_nonneg _))]
    _ = (Real.sqrt eps * Real.sqrt (vecEnergy w)) *
          (Real.sqrt eps * Real.sqrt (vecEnergy v)) := by
        rw [Real.sqrt_mul hε, Real.sqrt_mul hε]
    _ = (Real.sqrt eps * Real.sqrt eps) * Real.sqrt (vecEnergy w) *
          Real.sqrt (vecEnergy v) := by ring
    _ = eps * Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v) := by
        rw [Real.mul_self_sqrt hε]

/-- Normalized coherence of two images under a contracting completion.
`ρ` is the normalized coherence of the inputs, and `ε < 1` is the energy
deficit. -/
lemma filler_filler_ratio {k : ℕ} (eps ρ : ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hpert : ∀ w v : Fin k → ℝ,
      |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| ≤
        eps * Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v))
    (hlow : ∀ w : Fin k → ℝ, (1 - eps) * vecEnergy w ≤ vecEnergy (C *ᵥ w))
    (heps : eps < 1) (hε : 0 ≤ eps) (hρ : 0 ≤ ρ) (w v : Fin k → ℝ)
    (hab : |w ⬝ᵥ v| ≤ ρ * (Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v))) :
    |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)| ≤
      (ρ + eps) / (1 - eps) *
        (Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v))) := by
  have h1 : 0 < 1 - eps := by linarith
  have hsqrt1 : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr h1
  have hcoeff : 0 ≤ ρ + eps := by linarith
  have hdiv : ∀ u : Fin k → ℝ,
      Real.sqrt (vecEnergy u) ≤
        Real.sqrt (vecEnergy (C *ᵥ u)) / Real.sqrt (1 - eps) := by
    intro u
    have hlowu := hlow u
    have hsq : Real.sqrt ((1 - eps) * vecEnergy u) ≤ Real.sqrt (vecEnergy (C *ᵥ u)) :=
      Real.sqrt_le_sqrt hlowu
    rw [Real.sqrt_mul h1.le] at hsq
    exact (le_div_iff₀ hsqrt1).mpr (by simpa [mul_comm] using hsq)
  have hprod : Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v) ≤
      Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v)) / (1 - eps) := by
    have hw := hdiv w
    have hv := hdiv v
    calc Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v)
        ≤ (Real.sqrt (vecEnergy (C *ᵥ w)) / Real.sqrt (1 - eps)) *
            (Real.sqrt (vecEnergy (C *ᵥ v)) / Real.sqrt (1 - eps)) :=
          mul_le_mul hw hv (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hsqrt1.le)
      _ = Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v)) /
            (Real.sqrt (1 - eps) * Real.sqrt (1 - eps)) := by ring
      _ = Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v)) / (1 - eps) := by
          rw [Real.mul_self_sqrt h1.le]
  have htri : |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)| ≤
      |w ⬝ᵥ v| + |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| := by
    have hsum : (C *ᵥ w) ⬝ᵥ (C *ᵥ v) =
        (w ⬝ᵥ v) + ((C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v) := by ring
    calc |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)|
        = |(w ⬝ᵥ v) + ((C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v)| := by
          conv_lhs => rw [hsum]
      _ ≤ |w ⬝ᵥ v| + |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| :=
          abs_add_le (w ⬝ᵥ v) ((C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v)
  have hraw : |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)| ≤
      (ρ + eps) * (Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v)) := by
    calc |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)|
        ≤ |w ⬝ᵥ v| + |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| := htri
      _ ≤ ρ * (Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v)) +
            eps * Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v) :=
          add_le_add hab (hpert w v)
      _ = (ρ + eps) * (Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v)) := by ring
  have hscale := mul_le_mul_of_nonneg_left hprod hcoeff
  calc |(C *ᵥ w) ⬝ᵥ (C *ᵥ v)|
      ≤ (ρ + eps) * (Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v)) := hraw
    _ ≤ (ρ + eps) * (Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v)) /
          (1 - eps)) := hscale
    _ = (ρ + eps) / (1 - eps) *
          (Real.sqrt (vecEnergy (C *ᵥ w)) * Real.sqrt (vecEnergy (C *ᵥ v))) := by ring

/-- Normalized coherence of a fixed vector against `C w`, using
`‖(C - I) w‖² ≤ ε² ‖w‖²` and the energy lower bound on `C w`. -/
lemma leading_filler_ratio {k : ℕ} (eps θ : ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (r w : Fin k → ℝ)
    (hpert : ∀ v : Fin k → ℝ, vecEnergy ((C - 1) *ᵥ v) ≤ eps ^ 2 * vecEnergy v)
    (hlow : ∀ u : Fin k → ℝ, (1 - eps) * vecEnergy u ≤ vecEnergy (C *ᵥ u))
    (heps : eps < 1) (hε : 0 ≤ eps) (hθ : 0 ≤ θ)
    (hrw : |r ⬝ᵥ w| ≤ θ * (Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w))) :
    |r ⬝ᵥ (C *ᵥ w)| ≤
      (θ + eps) / Real.sqrt (1 - eps) *
        (Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy (C *ᵥ w))) := by
  have h1 : 0 < 1 - eps := by linarith
  have hsqrt1 : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr h1
  have hcoeff : 0 ≤ θ + eps := by linarith
  have hCw : C *ᵥ w = w + (C - 1) *ᵥ w := by
    have hsub : (C - 1) *ᵥ w = C *ᵥ w - w := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hsub]
    abel
  have hdot : r ⬝ᵥ (C *ᵥ w) = r ⬝ᵥ w + r ⬝ᵥ ((C - 1) *ᵥ w) := by
    rw [hCw, dotProduct_add]
  have hcauchy : |r ⬝ᵥ ((C - 1) *ᵥ w)| ≤
      Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy ((C - 1) *ᵥ w)) := by
    have hcs := energy_cauchy r ((C - 1) *ᵥ w)
    calc |r ⬝ᵥ ((C - 1) *ᵥ w)|
        = Real.sqrt ((r ⬝ᵥ ((C - 1) *ᵥ w)) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (vecEnergy r * vecEnergy ((C - 1) *ᵥ w)) := Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy ((C - 1) *ᵥ w)) := by
          rw [Real.sqrt_mul (vecEnergy_nonneg r)]
  have hsqrt_d : Real.sqrt (vecEnergy ((C - 1) *ᵥ w)) ≤
      eps * Real.sqrt (vecEnergy w) := by
    calc Real.sqrt (vecEnergy ((C - 1) *ᵥ w))
        ≤ Real.sqrt (eps ^ 2 * vecEnergy w) := Real.sqrt_le_sqrt (hpert w)
      _ = Real.sqrt (eps ^ 2) * Real.sqrt (vecEnergy w) := by
          rw [Real.sqrt_mul (sq_nonneg eps)]
      _ = |eps| * Real.sqrt (vecEnergy w) := by rw [Real.sqrt_sq_eq_abs]
      _ = eps * Real.sqrt (vecEnergy w) := by rw [abs_of_nonneg hε]
  have hdiff : |r ⬝ᵥ ((C - 1) *ᵥ w)| ≤
      eps * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) := by
    calc |r ⬝ᵥ ((C - 1) *ᵥ w)|
        ≤ Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy ((C - 1) *ᵥ w)) := hcauchy
      _ ≤ Real.sqrt (vecEnergy r) * (eps * Real.sqrt (vecEnergy w)) :=
          mul_le_mul_of_nonneg_left hsqrt_d (Real.sqrt_nonneg _)
      _ = eps * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) := by ring
  have hdiv : Real.sqrt (vecEnergy w) ≤
      Real.sqrt (vecEnergy (C *ᵥ w)) / Real.sqrt (1 - eps) := by
    have hsq : Real.sqrt ((1 - eps) * vecEnergy w) ≤ Real.sqrt (vecEnergy (C *ᵥ w)) :=
      Real.sqrt_le_sqrt (hlow w)
    rw [Real.sqrt_mul h1.le] at hsq
    exact (le_div_iff₀ hsqrt1).mpr (by simpa [mul_comm] using hsq)
  have hraw : |r ⬝ᵥ (C *ᵥ w)| ≤
      (θ + eps) * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) := by
    calc |r ⬝ᵥ (C *ᵥ w)|
        ≤ |r ⬝ᵥ w| + |r ⬝ᵥ ((C - 1) *ᵥ w)| := by rw [hdot]; exact abs_add_le _ _
      _ ≤ θ * (Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w)) +
            eps * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) :=
          add_le_add hrw hdiff
      _ = (θ + eps) * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) := by ring
  have hscale : (θ + eps) * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) ≤
      (θ + eps) * Real.sqrt (vecEnergy r) *
        (Real.sqrt (vecEnergy (C *ᵥ w)) / Real.sqrt (1 - eps)) := by
    have hnonneg : 0 ≤ (θ + eps) * Real.sqrt (vecEnergy r) :=
      mul_nonneg hcoeff (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hdiv hnonneg
  calc |r ⬝ᵥ (C *ᵥ w)|
      ≤ (θ + eps) * Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy w) := hraw
    _ ≤ (θ + eps) * Real.sqrt (vecEnergy r) *
          (Real.sqrt (vecEnergy (C *ᵥ w)) / Real.sqrt (1 - eps)) := hscale
    _ = (θ + eps) / Real.sqrt (1 - eps) *
          (Real.sqrt (vecEnergy r) * Real.sqrt (vecEnergy (C *ᵥ w))) := by ring

/-! ### Support of a triple-design column -/

lemma tripleNorm_pos (n : ℕ) : 0 < tripleNorm n := by
  unfold tripleNorm
  exact Real.sqrt_pos.mpr (by positivity)

lemma abs_signOf_real (b : Bool) : |(signOf b : ℝ)| = 1 := by
  cases b <;> simp [signOf]

lemma triple_support_ne {n : ℕ} (p : Fin (n + 3)) (q : Fin (n + 2)) (r : Fin (n + 1)) :
    p ≠ p.succAbove q ∧ p ≠ p.succAbove (q.succAbove r) ∧
      p.succAbove q ≠ p.succAbove (q.succAbove r) := by
  refine ⟨Fin.ne_succAbove p q, Fin.ne_succAbove p (q.succAbove r), ?_⟩
  intro h
  exact Fin.ne_succAbove q r (Fin.succAbove_right_injective h)

/-- A design column meets `v` on at most three coordinates, with weights `1, 2, 3`. -/
lemma triple_column_inner_le {n : ℕ} (v : Fin (n + 3) → ℝ) (a : TripleIndex n) :
    ∃ p q' r' : Fin (n + 3),
      p ≠ q' ∧ p ≠ r' ∧ q' ≠ r' ∧
      |v ⬝ᵥ (fun i => tripleDesign n i a)| ≤
        (|v p| + 2 * |v q'| + 3 * |v r'|) / tripleNorm n := by
  let p := a.1
  let q := a.2.1
  let r := a.2.2.1
  let σ := a.2.2.2.1
  let τ := a.2.2.2.2
  let q' := p.succAbove q
  let r' := p.succAbove (q.succAbove r)
  obtain ⟨hpq, hpr, hqr⟩ := triple_support_ne p q r
  have hpval : (tripleCol a p : ℝ) = 1 := by
    exact_mod_cast tripleCol_at_fst a
  have hqval : (tripleCol a q' : ℝ) = 2 * (signOf σ : ℝ) := by
    have hZ : tripleCol a q' = 2 * signOf σ := by
      simpa [tripleCol, p, q, r, σ, q'] using
        tripleInt_at_q a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
    rw [hZ]
    push_cast
    rfl
  have hrval : (tripleCol a r' : ℝ) = 3 * (signOf τ : ℝ) := by
    have hZ : tripleCol a r' = 3 * signOf τ := by
      simpa [tripleCol, p, q, r, τ, r'] using
        tripleInt_at_r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2
    rw [hZ]
    push_cast
    rfl
  let f : Fin (n + 3) → ℝ := fun i => v i * (tripleCol a i : ℝ)
  have hsubset : ∑ i, f i = ∑ i ∈ insert p (insert q' {r'}), f i := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
    have hip : i ≠ p := by
      intro hip
      exact hi (Finset.mem_insert.mpr (Or.inl hip))
    have hiq : i ≠ q' := by
      intro hiq
      exact hi (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl hiq))))
    have hir : i ≠ r' := by
      intro hir
      exact hi (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hir)))))
    have hcol : tripleCol a i = 0 := by
      simpa [tripleCol, p, q, r, σ, τ, q', r'] using
        tripleInt_at_other a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hip hiq hir
    simp [f, hcol]
  have hp_not : p ∉ insert q' ({r'} : Finset _) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | hmem
    · exact hpq h
    · exact hpr (Finset.mem_singleton.mp hmem)
  have hq_not : q' ∉ ({r'} : Finset _) := by
    intro hmem
    exact hqr (Finset.mem_singleton.mp hmem)
  have hthree : ∑ i ∈ insert p (insert q' {r'}), f i = f p + f q' + f r' := by
    rw [Finset.sum_insert hp_not, Finset.sum_insert hq_not, Finset.sum_singleton]
    ring
  have habs : |f p + f q' + f r'| ≤ |v p| + 2 * |v q'| + 3 * |v r'| := by
    have h1 : |f p| = |v p| := by simp [f, hpval]
    have h2 : |f q'| = 2 * |v q'| := by
      rw [show f q' = v q' * (2 * (signOf σ : ℝ)) by simp [f, hqval], abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_signOf_real]
      ring
    have h3 : |f r'| = 3 * |v r'| := by
      rw [show f r' = v r' * (3 * (signOf τ : ℝ)) by simp [f, hrval], abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_signOf_real]
      ring
    have hAB := abs_add_le (f p) (f q')
    have hABC := abs_add_le (f p + f q') (f r')
    linarith
  have hsum_abs : |∑ i, f i| ≤ |v p| + 2 * |v q'| + 3 * |v r'| := by
    rw [hsubset, hthree]
    exact habs
  have hdot : v ⬝ᵥ (fun i => tripleDesign n i a) = (∑ i, f i) / tripleNorm n := by
    simp only [dotProduct, tripleDesign]
    have hterm : ∀ i, v i * ((tripleCol a i : ℝ) / tripleNorm n) = f i / tripleNorm n := by
      intro i
      simp [f]
      ring
    simp_rw [hterm]
    rw [Finset.sum_div]
  refine ⟨p, q', r', hpq, hpr, hqr, ?_⟩
  rw [hdot, abs_div, abs_of_pos (tripleNorm_pos n)]
  exact div_le_div_of_nonneg_right hsum_abs (tripleNorm_pos n).le

lemma tripleDesignFin_column_inner_le {n : ℕ} (v : Fin (n + 3) → ℝ)
    (j : Fin (tripleCount n)) :
    ∃ p q' r' : Fin (n + 3),
      p ≠ q' ∧ p ≠ r' ∧ q' ≠ r' ∧
      |v ⬝ᵥ (fun i => tripleDesignFin n i j)| ≤
        (|v p| + 2 * |v q'| + 3 * |v r'|) / tripleNorm n := by
  simpa [tripleDesignFin] using triple_column_inner_le v ((tripleEquiv n).symm j)

lemma dotProduct_reindex {k n : ℕ} (e : Fin k ≃ Fin (n + 3))
    (v : Fin k → ℝ) (col : Fin (n + 3) → ℝ) :
    v ⬝ᵥ (fun i => col (e i)) = (fun i => v (e.symm i)) ⬝ᵥ col := by
  simp only [dotProduct]
  have h : ∀ i, v i * col (e i) = v (e.symm (e i)) * col (e i) := by
    intro i
    rw [e.symm_apply_apply]
  simp_rw [h]
  exact e.sum_comp fun j => v (e.symm j) * col j

/-- The same three-coordinate bound after the row reindexing used by the frame.
The support coordinates are pulled back by `e.symm`. -/
lemma reindexed_triple_column_inner_le {k n : ℕ} (e : Fin k ≃ Fin (n + 3))
    (v : Fin k → ℝ) (j : Fin (tripleCount n)) :
    ∃ p q' r' : Fin k, p ≠ q' ∧ p ≠ r' ∧ q' ≠ r' ∧
      |v ⬝ᵥ (fun i => (tripleDesignFin n).submatrix e id i j)| ≤
        (|v p| + 2 * |v q'| + 3 * |v r'|) / tripleNorm n := by
  have hfun : ∀ i, (tripleDesignFin n).submatrix e id i j = tripleDesignFin n (e i) j := by
    intro i
    simp [Matrix.submatrix_apply]
  obtain ⟨p0, q0, r0, hpq, hpr, hqr, hle⟩ :=
    tripleDesignFin_column_inner_le (fun i => v (e.symm i)) j
  refine ⟨e.symm p0, e.symm q0, e.symm r0, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hpq (e.symm.injective h)
  · intro h
    exact hpr (e.symm.injective h)
  · intro h
    exact hqr (e.symm.injective h)
  · have hleft : v ⬝ᵥ (fun i => (tripleDesignFin n).submatrix e id i j) =
        (fun i => v (e.symm i)) ⬝ᵥ (fun i => tripleDesignFin n i j) := by
      simp only [dotProduct]
      have h := dotProduct_reindex e v (fun i => tripleDesignFin n i j)
      simp only [dotProduct] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfun]
    rw [hleft]
    exact hle

/-! ### Leading columns of the scaled triangular block -/

lemma frame_eps_lt_one {m : ℕ} (hm : 3 ≤ m) :
    45 / (16 * (wideDim m : ℝ)) < 1 := by
  have hk := wideDim_ge_nine hm
  have hkR : (9 : ℝ) ≤ (wideDim m : ℝ) := by exact_mod_cast hk
  rw [div_lt_one (by positivity)]
  nlinarith

lemma wideC_le_one_div_two_mul {m : ℕ} (hm : 2 ≤ m) :
    wideC m ≤ 1 / (2 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold wideC
  rw [div_le_div_iff₀ (wideDen_pos m) (by positivity)]
  nlinarith

lemma wideC_mul_alpha_le_diag_div {m : ℕ} (hm : 2 ≤ m) (j : Fin (wideDim m)) :
    wideC m * wideAlpha m ≤ wideDiagNat m j / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hhalf := wideDiag_half_lower hm j.isLt
  calc wideC m * wideAlpha m
      ≤ (1 / (2 * (m : ℝ))) * wideAlpha m :=
        mul_le_mul_of_nonneg_right (wideC_le_one_div_two_mul hm) (wideAlpha_pos hm).le
    _ = (wideAlpha m / 2) / (m : ℝ) := by ring
    _ ≤ wideDiagNat m j / (m : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hhalf]

lemma scaledBlock_diag {m : ℕ} (j : Fin (wideDim m)) :
    scaledBlock m j j = 3 * wideDiagNat m j := by
  unfold scaledBlock
  rw [Matrix.smul_apply, wideTriangular_diag, smul_eq_mul]

lemma scaledBlock_offdiag_abs_le {m : ℕ} (hm : 2 ≤ m) {i j : Fin (wideDim m)}
    (hij : i ≠ j) :
    |scaledBlock m i j| ≤ 3 * wideC m * wideAlpha m := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  unfold scaledBlock
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h3]
  by_cases hlt : (i : ℕ) < (j : ℕ)
  · unfold wideTriangular
    rw [if_neg hij, if_pos hlt, abs_mul, abs_neg]
    have hc : 0 ≤ wideC m := (wideC_pos hm).le
    have hd : 0 ≤ wideDiagNat m i := (wideDiag_pos hm i).le
    rw [abs_of_nonneg hc, abs_of_nonneg hd]
    have hda := wideDiag_le_alpha hm i
    have : wideC m * wideDiagNat m i ≤ wideC m * wideAlpha m :=
      mul_le_mul_of_nonneg_left hda hc
    linarith
  · rw [wideTriangular_upper (by omega : (j : ℕ) < (i : ℕ)), abs_zero]
    nlinarith [wideC_pos hm, wideAlpha_pos hm]

lemma scaledBlock_col_energy_ge {m : ℕ} (j : Fin (wideDim m)) :
    (scaledBlock m j j) ^ 2 ≤ vecEnergy (fun i => scaledBlock m i j) := by
  unfold vecEnergy
  refine Finset.single_le_sum (f := fun i => (scaledBlock m i j) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- `|v p| + 2|v q'| + 3|v r'|` for three distinct coordinates. At most one of
them is the diagonal index `j`, so the sum is at most `3 |v j| + 3 δ` when
every off-diagonal entry is at most `δ` and `δ ≤ |v j|`. -/
lemma support_weight_le {k : ℕ} (v : Fin k → ℝ) (j p q' r' : Fin k)
    (hpq : p ≠ q') (hpr : p ≠ r') (hqr : q' ≠ r')
    {D δ : ℝ} (hj : |v j| ≤ D) (hoff : ∀ i, i ≠ j → |v i| ≤ δ) (hδD : δ ≤ D) :
    |v p| + 2 * |v q'| + 3 * |v r'| ≤ 3 * D + 3 * δ := by
  rcases eq_or_ne j r' with hr | hr
  · exact (by
      have hp : |v p| ≤ δ := hoff p (fun h => hpr (h.trans hr))
      have hq : |v q'| ≤ δ := hoff q' (fun h => hqr (h.trans hr))
      have hrv : |v r'| ≤ D := by rw [← hr]; exact hj
      nlinarith [hδD])
  · rcases eq_or_ne j q' with hqj | hqj
    · exact (by
        have hp : |v p| ≤ δ := hoff p (fun h => hpq (h.trans hqj))
        have hrv : |v r'| ≤ δ := hoff r' (fun h => hqr (h.trans hqj).symm)
        have hqv : |v q'| ≤ D := by rw [← hqj]; exact hj
        nlinarith [hδD])
    · rcases eq_or_ne j p with hpj | hpj
      · exact (by
          have hq : |v q'| ≤ δ := hoff q' (fun h => hpq (h.trans hpj).symm)
          have hrv : |v r'| ≤ δ := hoff r' (fun h => hpr (h.trans hpj).symm)
          have hpv : |v p| ≤ D := by rw [← hpj]; exact hj
          nlinarith [hδD])
      · exact (by
          have hp : |v p| ≤ δ := hoff p (Ne.symm hpj)
          have hq : |v q'| ≤ δ := hoff q' (Ne.symm hqj)
          have hrv : |v r'| ≤ δ := hoff r' (Ne.symm hr)
          nlinarith [hδD])

lemma tripleDesignFin_energy_norm (n : ℕ) (j : Fin (tripleCount n)) :
    vecEnergy (fun i => tripleDesignFin n i j) = 14 / tripleNorm n ^ 2 := by
  rw [tripleDesignFin_col_energy, tripleNorm_sq, div_eq_div_iff (by positivity) (by positivity)]
  ring

lemma sqrt_fourteen_over_norm (n : ℕ) :
    Real.sqrt (14 / tripleNorm n ^ 2) = Real.sqrt 14 / tripleNorm n := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 14), Real.sqrt_sq (tripleNorm_pos n).le]

lemma reindexed_triple_energy {k n : ℕ} (e : Fin k ≃ Fin (n + 3))
    (j : Fin (tripleCount n)) :
    vecEnergy (fun i => (tripleDesignFin n).submatrix e id i j) =
      14 / tripleNorm n ^ 2 := by
  rw [(design_reindex e (tripleDesignFin n) (tripleDesignFin_gram n)).2.1 j]
  exact tripleDesignFin_energy_norm n j

/-- `|⟨r_j, w⟩| ≤ 3(1 + 1/m) / √14 · √(‖r_j‖²) √(‖w‖²)` for a reindexed
triple-design column `w` and a scaled leading column `r_j`. -/
lemma scaledBlock_design_inner_le {m n : ℕ} (hm : 2 ≤ m)
    (e : Fin (wideDim m) ≃ Fin (n + 3))
    (j : Fin (wideDim m)) (a : Fin (tripleCount n)) :
    |(fun i => scaledBlock m i j) ⬝ᵥ
        (fun i => (tripleDesignFin n).submatrix e id i a)| ≤
      3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 *
        (Real.sqrt (vecEnergy (fun i => scaledBlock m i j)) *
          Real.sqrt (vecEnergy (fun i => (tripleDesignFin n).submatrix e id i a))) := by
  set r : Fin (wideDim m) → ℝ := fun i => scaledBlock m i j
  set w : Fin (wideDim m) → ℝ := fun i => (tripleDesignFin n).submatrix e id i a
  obtain ⟨p, q', r', hpq, hpr, hqr, hle⟩ := reindexed_triple_column_inner_le e r a
  have hDabs : |r j| = 3 * wideDiagNat m j := by
    unfold r
    rw [scaledBlock_diag]
    exact abs_of_nonneg (mul_nonneg (by norm_num) (wideDiag_pos hm j).le)
  set δ : ℝ := 3 * wideC m * wideAlpha m
  have hδ_div : δ ≤ |r j| / (m : ℝ) := by
    rw [hDabs]
    have hca := wideC_mul_alpha_le_diag_div hm j
    calc 3 * wideC m * wideAlpha m ≤ 3 * (wideDiagNat m j / (m : ℝ)) := by
          nlinarith [hca]
      _ = (3 * wideDiagNat m j) / (m : ℝ) := by ring
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hδD : δ ≤ |r j| := hδ_div.trans (div_le_self (abs_nonneg _) hm1)
  have hoff : ∀ i, i ≠ j → |r i| ≤ δ := fun i hi => scaledBlock_offdiag_abs_le hm hi
  have hweight := support_weight_le r j p q' r' hpq hpr hqr (le_refl |r j|) hoff hδD
  have hsum : |r p| + 2 * |r q'| + 3 * |r r'| ≤
      3 * |r j| * (1 + 1 / (m : ℝ)) := by
    have hδm : 3 * δ ≤ 3 * (|r j| / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hδ_div (by norm_num)
    have hring : 3 * |r j| + 3 * (|r j| / (m : ℝ)) =
        3 * |r j| * (1 + 1 / (m : ℝ)) := by ring
    linarith [hweight, hδm, hring]
  have hjsq : |r j| ≤ Real.sqrt (vecEnergy r) := by
    have hsq : |r j| ^ 2 ≤ vecEnergy r := by
      rw [sq_abs]
      exact scaledBlock_col_energy_ge j
    have hsqrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_abs] at hsqrt
    exact hsqrt
  have hT : 0 < tripleNorm n := tripleNorm_pos n
  have hEw : vecEnergy w = 14 / tripleNorm n ^ 2 := reindexed_triple_energy e a
  have hsqrtw : Real.sqrt (vecEnergy w) = Real.sqrt 14 / tripleNorm n := by
    rw [hEw, sqrt_fourteen_over_norm]
  have hnum : |r p| + 2 * |r q'| + 3 * |r r'| ≤
      3 * Real.sqrt (vecEnergy r) * (1 + 1 / (m : ℝ)) := by
    have hpos : 0 ≤ 1 + 1 / (m : ℝ) := by positivity
    have hmul : 3 * |r j| * (1 + 1 / (m : ℝ)) ≤
        3 * Real.sqrt (vecEnergy r) * (1 + 1 / (m : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjsq (by norm_num)) hpos
    exact hsum.trans hmul
  have hdot_le : |r ⬝ᵥ w| ≤
      (3 * Real.sqrt (vecEnergy r) * (1 + 1 / (m : ℝ))) / tripleNorm n := by
    exact (hle.trans (div_le_div_of_nonneg_right hnum hT.le))
  have hident : (3 * Real.sqrt (vecEnergy r) * (1 + 1 / (m : ℝ))) / tripleNorm n =
      3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 *
        (Real.sqrt (vecEnergy r) * (Real.sqrt 14 / tripleNorm n)) := by
    have h14 : Real.sqrt 14 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp [hT.ne', h14]
  rw [hident, ← hsqrtw] at hdot_le
  exact hdot_le

/-! ### The scaled frame with filler-pair coherence -/

/-- For every `m ≥ 3`, the scaled triple-design frame carries filler–filler
normalized coherence at most `(13/14 + ε)/(1 - ε)` and leading–filler
normalized coherence at most `(3(1 + 1/m)/√14 + ε)/√(1 - ε)`, with
`ε = 45 / (16 k)`.

Leading–leading pairs are not bounded. No coherence bound on the whole frame
is claimed. This does not close outcome 1 or outcome 3. -/
theorem scaled_triple_frame_filler_coherence {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : Matrix (Fin (wideDim m)) (Fin (wideDim m + tripleCount (wideDim m - 3))) ℝ,
    ∃ C : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ,
    ∃ W : Matrix (Fin (wideDim m)) (Fin (tripleCount (wideDim m - 3))) ℝ,
    ∃ x : Fin (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)).card → ℝ,
      OrthogonalRows A ∧
      (∀ i j : Fin (wideDim m), A i (j.castAdd _) = scaledBlock m i j) ∧
      (∀ (i : Fin (wideDim m)) (j : Fin (tripleCount (wideDim m - 3))),
        A i (j.natAdd (wideDim m)) = (C * W) i j) ∧
      Cᵀ = C ∧ scaledBlock m * (scaledBlock m)ᵀ + C * Cᵀ = 1 ∧
      frobEnergy (scaledBlock m) ≤ 45 / (16 * (wideDim m : ℝ)) ∧
      (∀ w v : Fin (wideDim m) → ℝ,
        (C *ᵥ w) ⬝ᵥ (C *ᵥ v) = w ⬝ᵥ v - ((scaledBlock m)ᵀ *ᵥ w) ⬝ᵥ ((scaledBlock m)ᵀ *ᵥ v)) ∧
      (∀ w : Fin (wideDim m) → ℝ,
        (1 - frobEnergy (scaledBlock m)) * vecEnergy w ≤ vecEnergy (C *ᵥ w) ∧
          vecEnergy (C *ᵥ w) ≤ vecEnergy w) ∧
      (∀ v : Fin (wideDim m) → ℝ,
        vecEnergy ((C - 1) *ᵥ v) ≤ frobEnergy (scaledBlock m) ^ 2 * vecEnergy v) ∧
      W * Wᵀ = 1 ∧
      (∀ j, vecEnergy (fun i => W i j) =
        1 / (4 * (((wideDim m : ℝ) - 1) * ((wideDim m : ℝ) - 2)))) ∧
      (∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
        13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
          Real.sqrt (vecEnergy (fun i => W i b)))) ∧
      cpqrSet A = widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m) ∧
      vecEnergy (selectedCols A
        (widePrefix (wideDim m + tripleCount (wideDim m - 3)) (wideDim m)) *ᵥ x) = 1 ∧
      wideGrowthLower m ^ 2 / 9 ≤ vecEnergy x ∧
      (∀ a b : Fin (tripleCount (wideDim m - 3)), a ≠ b →
        |∑ i, A i (a.natAdd (wideDim m)) * A i (b.natAdd (wideDim m))| ≤
          (13 / 14 + 45 / (16 * (wideDim m : ℝ))) / (1 - 45 / (16 * (wideDim m : ℝ))) *
            (Real.sqrt (vecEnergy (fun i => A i (a.natAdd (wideDim m)))) *
              Real.sqrt (vecEnergy (fun i => A i (b.natAdd (wideDim m)))))) ∧
      ∀ (j : Fin (wideDim m)) (a : Fin (tripleCount (wideDim m - 3))),
        |∑ i, A i (j.castAdd _) * A i (a.natAdd (wideDim m))| ≤
          (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + 45 / (16 * (wideDim m : ℝ))) /
              Real.sqrt (1 - 45 / (16 * (wideDim m : ℝ))) *
            (Real.sqrt (vecEnergy (fun i => A i (j.castAdd _))) *
              Real.sqrt (vecEnergy (fun i => A i (a.natAdd (wideDim m))))) := by
  have hm2 : 2 ≤ m := by omega
  have hk9 := wideDim_ge_nine hm
  set k := wideDim m with hkdef
  set n := k - 3 with hndef
  have hkn : k = n + 3 := by omega
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk9
  have hnR : (n : ℝ) = (k : ℝ) - 3 := by
    rw [hndef, Nat.cast_sub (by omega : 3 ≤ k)]
    norm_num
  let e : Fin k ≃ Fin (n + 3) := finCongr hkn
  let W : Matrix (Fin k) (Fin (tripleCount n)) ℝ := (tripleDesignFin n).submatrix e id
  obtain ⟨hWW, hWE, hWI⟩ := design_reindex e (tripleDesignFin n) (tripleDesignFin_gram n)
  have hWenergy : ∀ j, vecEnergy (fun i => W i j) =
      1 / (4 * (((k : ℝ) - 1) * ((k : ℝ) - 2))) := by
    intro j
    show vecEnergy (fun i => (tripleDesignFin n).submatrix e id i j) = _
    rw [hWE j, tripleDesignFin_col_energy, hnR]
    ring_nf
  have hWcoh : ∀ a b, a ≠ b → |∑ i, W i a * W i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => W i a)) *
        Real.sqrt (vecEnergy (fun i => W i b))) := by
    intro a b hab
    show |∑ i, (tripleDesignFin n).submatrix e id i a *
      (tripleDesignFin n).submatrix e id i b| ≤
      13 / 14 * (Real.sqrt (vecEnergy (fun i => (tripleDesignFin n).submatrix e id i a)) *
        Real.sqrt (vecEnergy (fun i => (tripleDesignFin n).submatrix e id i b)))
    rw [hWI a b, hWE a, hWE b]
    exact tripleDesignFin_coherence n hab
  have hcol : ∀ j, vecEnergy (fun q => W q j) ≤ (3 : ℝ) ^ 2 / (16 * (k : ℝ) ^ 2) := by
    intro j
    rw [hWenergy j]
    exact triple_energy_le_threshold (by linarith)
  have hfrob1 := scaledBlock_frob_le_one hm
  obtain ⟨C, hsym, hCC, hinner, hsand, hpert⟩ := symmetric_completion (scaledBlock m) hfrob1
  have hcontr : ∀ w : Fin k → ℝ, vecEnergy (C *ᵥ w) ≤ vecEnergy w := fun w => (hsand w).2
  have hCC' : ((3 : ℝ) • wideTriangular m) * ((3 : ℝ) • wideTriangular m)ᵀ + C * Cᵀ = 1 := hCC
  obtain ⟨x, hA, hset, himg, hgrow⟩ :=
    wide_scaled_design_adverse hm2 (by norm_num : (0 : ℝ) < 3) C hCC' hcontr W hWW hcol
  set A := designFrame (scaledBlock m) C W
  let eps : ℝ := 45 / (16 * (k : ℝ))
  have hfrob_eps : frobEnergy (scaledBlock m) ≤ eps := by
    simpa [eps, hkdef] using scaledBlock_frob_le hm2
  have hε0 : 0 ≤ eps := (frobEnergy_nonneg _).trans hfrob_eps
  have hε1 : eps < 1 := by simpa [eps, hkdef] using frame_eps_lt_one hm
  have hperturb : ∀ w v : Fin k → ℝ,
      |(C *ᵥ w) ⬝ᵥ (C *ᵥ v) - w ⬝ᵥ v| ≤
        eps * Real.sqrt (vecEnergy w) * Real.sqrt (vecEnergy v) :=
    fun w v => completion_inner_perturb eps (scaledBlock m) C hinner hfrob_eps w v
  have hlow : ∀ w : Fin k → ℝ, (1 - eps) * vecEnergy w ≤ vecEnergy (C *ᵥ w) := by
    intro w
    have hcmp : 1 - eps ≤ 1 - frobEnergy (scaledBlock m) := by linarith
    exact (mul_le_mul_of_nonneg_right hcmp (vecEnergy_nonneg w)).trans (hsand w).1
  have hpertEps : ∀ v : Fin k → ℝ,
      vecEnergy ((C - 1) *ᵥ v) ≤ eps ^ 2 * vecEnergy v := by
    intro v
    have hsq : frobEnergy (scaledBlock m) ^ 2 ≤ eps ^ 2 := by
      nlinarith [hε0, frobEnergy_nonneg (scaledBlock m), hfrob_eps]
    exact (hpert v).trans (mul_le_mul_of_nonneg_right hsq (vecEnergy_nonneg v))
  have hff : ∀ a b : Fin (tripleCount n), a ≠ b →
      |∑ i, A i (a.natAdd k) * A i (b.natAdd k)| ≤
        (13 / 14 + eps) / (1 - eps) *
          (Real.sqrt (vecEnergy (fun i => A i (a.natAdd k))) *
            Real.sqrt (vecEnergy (fun i => A i (b.natAdd k)))) := by
    intro a b hab
    have hwa : (fun i => A i (a.natAdd k)) = C *ᵥ (fun i => W i a) :=
      designFrame_right_col (scaledBlock m) C W a
    have hwb : (fun i => A i (b.natAdd k)) = C *ᵥ (fun i => W i b) :=
      designFrame_right_col (scaledBlock m) C W b
    have hratio := filler_filler_ratio eps (13 / 14) C hperturb hlow hε1 hε0
      (by norm_num) (fun i => W i a) (fun i => W i b) ?_
    · simp_rw [congrFun hwa, congrFun hwb]
      simpa [dotProduct, vecEnergy] using hratio
    · simpa [dotProduct, vecEnergy] using hWcoh a b hab
  have hlf : ∀ (j : Fin k) (a : Fin (tripleCount n)),
      |∑ i, A i (j.castAdd (tripleCount n)) * A i (a.natAdd k)| ≤
        (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14 + eps) / Real.sqrt (1 - eps) *
          (Real.sqrt (vecEnergy (fun i => A i (j.castAdd (tripleCount n)))) *
            Real.sqrt (vecEnergy (fun i => A i (a.natAdd k)))) := by
    intro j a
    have hrj : (fun i => A i (j.castAdd (tripleCount n))) = fun i => scaledBlock m i j := by
      ext i
      exact designFrame_left (scaledBlock m) C W i j
    have hwa : (fun i => A i (a.natAdd k)) = C *ᵥ (fun i => W i a) :=
      designFrame_right_col (scaledBlock m) C W a
    have hratio := leading_filler_ratio eps
      (3 * (1 + 1 / (m : ℝ)) / Real.sqrt 14) C
      (fun i => scaledBlock m i j) (fun i => W i a) hpertEps hlow hε1 hε0
      (by positivity) (scaledBlock_design_inner_le hm2 e j a)
    simp_rw [congrFun hrj, congrFun hwa]
    simpa [dotProduct, vecEnergy] using hratio
  refine ⟨A, C, W, x, hA, designFrame_left _ _ _, designFrame_right _ _ _, hsym, hCC,
    scaledBlock_frob_le hm2, hinner, hsand, hpert, hWW, hWenergy, hWcoh, hset, himg, ?_,
    hff, hlf⟩
  calc wideGrowthLower m ^ 2 / 9 = wideGrowthLower m ^ 2 / (3 : ℝ) ^ 2 := by norm_num
    _ ≤ vecEnergy x := hgrow

end StructuredColumnSelection
