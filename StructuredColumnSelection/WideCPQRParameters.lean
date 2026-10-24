import StructuredColumnSelection.PrefixInverse

/-! Exact scalar and triangular algebra for the wide CPQR construction.
No claim about the actual greedy output is made by this module alone. -/
namespace StructuredColumnSelection
open Classical Finset
open scoped Matrix

def wideDim (m : ℕ) : ℕ := m*m
noncomputable def wideEps (m : ℕ) : ℝ := (4*(m:ℝ)^2-1)/(4*(m:ℝ)^2+1)
noncomputable def wideC (m : ℕ) : ℝ := (2*(m:ℝ))/(4*(m:ℝ)^2+1)
noncomputable def wideAlpha (m : ℕ) : ℝ := 1/(2*(wideDim m:ℝ))
noncomputable def wideDiagNat (m i : ℕ) : ℝ := wideAlpha m * wideEps m ^ i

noncomputable def wideTriangular (m : ℕ) : Matrix (Fin (wideDim m)) (Fin (wideDim m)) ℝ :=
  fun i j => if i=j then wideDiagNat m i else
    if (i:ℕ)<(j:ℕ) then -wideC m * wideDiagNat m i else 0

lemma wideDim_pos {m : ℕ} (hm : 2 ≤ m) : 0 < wideDim m := by unfold wideDim; positivity
lemma wideDen_pos (m : ℕ) : (0:ℝ) < 4*(m:ℝ)^2+1 := by positivity
lemma wideEps_pos {m : ℕ} (hm : 2 ≤ m) : 0 < wideEps m := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  apply div_pos ?_ (wideDen_pos m)
  nlinarith
lemma wideEps_lt_one (m : ℕ) : wideEps m < 1 := by
  apply (div_lt_one (wideDen_pos m)).mpr
  linarith
lemma wideC_pos {m : ℕ} (hm : 2 ≤ m) : 0 < wideC m := by
  unfold wideC
  apply div_pos ?_ (wideDen_pos m)
  exact_mod_cast (show 0 < 2*m by omega)
lemma wideC_le_one {m : ℕ} (hm : 2 ≤ m) : wideC m ≤ 1 := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  apply (div_le_one (wideDen_pos m)).mpr
  nlinarith
lemma wideC_lower {m : ℕ} (hm : 2 ≤ m) : 1/(3*(m:ℝ)) ≤ wideC m := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  unfold wideC
  apply (div_le_div_iff₀ (by positivity) (wideDen_pos m)).mpr
  nlinarith
lemma wide_coupling_budget {m : ℕ} (hm : 2 ≤ m) : wideC m ^ 2 + wideEps m ^ 2 < 1 := by
  have hid : 1-(wideC m ^ 2+wideEps m ^ 2) =
      12*(m:ℝ)^2/(4*(m:ℝ)^2+1)^2 := by
    unfold wideC wideEps
    field_simp
    ring
  have hp : (0:ℝ) < 12*(m:ℝ)^2/(4*(m:ℝ)^2+1)^2 := by
    have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  linarith
lemma wideAlpha_pos {m : ℕ} (hm : 2 ≤ m) : 0 < wideAlpha m := by
  have hk := wideDim_pos hm
  unfold wideAlpha
  positivity
lemma wideDiag_pos {m : ℕ} (hm : 2 ≤ m) (i : ℕ) : 0 < wideDiagNat m i :=
  mul_pos (wideAlpha_pos hm) (pow_pos (wideEps_pos hm) i)
lemma wideDiag_le_alpha {m : ℕ} (hm : 2 ≤ m) (i : ℕ) : wideDiagNat m i ≤ wideAlpha m := by
  have hp := pow_le_one₀ (wideEps_pos hm).le (wideEps_lt_one m).le (n:=i)
  exact (mul_le_mul_of_nonneg_left hp (wideAlpha_pos hm).le).trans_eq (mul_one _)
lemma wideDiag_succ (m i : ℕ) : wideDiagNat m (i+1) = wideEps m * wideDiagNat m i := by
  unfold wideDiagNat
  rw [pow_succ]
  ring
lemma wideBernoulli_lower (m : ℕ) :
    (1:ℝ)/2 < 1-(wideDim m:ℝ)*(1-wideEps m) := by
  have hd := wideDen_pos m
  have heq : 1-(wideDim m:ℝ)*(1-wideEps m) =
      (2*(m:ℝ)^2+1)/(4*(m:ℝ)^2+1) := by
    unfold wideDim wideEps
    push_cast
    field_simp
    ring
  rw [heq]
  apply (div_lt_div_iff₀ (by norm_num : (0:ℝ)<2) hd).mpr
  nlinarith

/-- Every leading diagonal stays above half its initial scale. -/
lemma wideDiag_half_lower {m : ℕ} (hm : 2 ≤ m) {i : ℕ} (hi : i < wideDim m) :
    wideAlpha m / 2 < wideDiagNat m i := by
  have hε := wideEps_pos hm
  have hε1 := wideEps_lt_one m
  have hb := one_add_mul_le_pow (a := wideEps m-1) (by linarith) i
  have hb' : 1+(i:ℝ)*(wideEps m-1) ≤ wideEps m ^ i := by
    simpa only [add_sub_cancel] using hb
  have hiR : (i:ℝ) ≤ wideDim m := by exact_mod_cast hi.le
  have hg := wideBernoulli_lower m
  have hpow : (1:ℝ)/2 < wideEps m^i := by
    have hc := mul_nonneg (sub_nonneg.mpr hiR) (sub_nonneg.mpr hε1.le)
    nlinarith
  simpa only [wideDiagNat, div_eq_mul_inv, one_mul] using
    mul_lt_mul_of_pos_left hpow (wideAlpha_pos hm)

lemma wideTriangular_upper {m : ℕ} {i j : Fin (wideDim m)} (hji : (j:ℕ)<(i:ℕ)) :
    wideTriangular m i j = 0 := by
  have hne : i≠j := fun h => by subst j; omega
  have hn : ¬ (i:ℕ)<(j:ℕ) := by omega
  simp [wideTriangular,hne,hn]
lemma wideTriangular_diag (m : ℕ) (i : Fin (wideDim m)) :
    wideTriangular m i i = wideDiagNat m i := by simp [wideTriangular]

end StructuredColumnSelection
