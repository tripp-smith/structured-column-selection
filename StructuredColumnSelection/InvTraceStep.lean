import StructuredColumnSelection.ResidualEnergy

/-! Inverse-trace increment for one appended column.

Standard CPQR maximizes the residual. The inverse-trace increment is
`(1 + ‖G⁻¹ Bᵀ v‖²) / residual`, so that numerator is a different pivot
score. These lemmas do not bound CPQR and do not close outcome 3. -/

namespace StructuredColumnSelection
open Classical Finset Matrix
open scoped Matrix

lemma trace_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : β ≃ α) (M : Matrix α α ℝ) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.sum_comp fun i => M i i

lemma trace_fromBlocks {t : ℕ}
    (A : Matrix (Fin t) (Fin t) ℝ) (B : Matrix (Fin t) (Fin 1) ℝ)
    (C : Matrix (Fin 1) (Fin t) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp only [Matrix.trace]
  rw [Fintype.sum_sum_type]
  refine congrArg₂ HAdd.hAdd ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.fromBlocks_apply₁₁]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.fromBlocks_apply₂₂]

lemma trace_fin_one (D : Matrix (Fin 1) (Fin 1) ℝ) : D.trace = D 0 0 := by
  simp [Matrix.trace, Fin.sum_univ_one]

lemma inv_fin_one_entry (a : ℝ) (ha : a ≠ 0) :
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => a
    D⁻¹ 0 0 = a⁻¹ := by
  intro D
  have hdet : D.det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact ha
  have hmul := Matrix.mul_nonsing_inv (A := D) (Ne.isUnit hdet)
  have h00 : (D * D⁻¹) 0 0 = 1 := by
    have h := congr_fun (congr_fun hmul 0) 0
    simpa [Matrix.one_apply] using h
  have hprod : (D * D⁻¹) 0 0 = D 0 0 * D⁻¹ 0 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_one]
  rw [hprod] at h00
  have hD0 : D 0 0 = a := rfl
  rw [hD0] at h00
  exact eq_inv_of_mul_eq_one_right h00

lemma schur_corner {t : ℕ} (G : Matrix (Fin t) (Fin t) ℝ) (w : Fin t → ℝ) (α : ℝ)
    [Invertible G] :
    let C : Matrix (Fin 1) (Fin t) ℝ := fun _ q => w q
    let B : Matrix (Fin t) (Fin 1) ℝ := fun p _ => w p
    let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => α
    (D - C * ⅟G * B) 0 0 = α - (w ⬝ᵥ (⅟G *ᵥ w)) := by
  intro C B D
  set Ginv : Matrix (Fin t) (Fin t) ℝ := ⅟G
  have hsub : (D - C * Ginv * B) 0 0 = D 0 0 - (C * Ginv * B) 0 0 :=
    Matrix.sub_apply _ _ 0 0
  have hD : D 0 0 = α := rfl
  have hmul : (C * Ginv * B) 0 0 = w ⬝ᵥ (Ginv *ᵥ w) := by
    have hmul1 : (C * Ginv * B) 0 0 =
        ∑ q : Fin t, (∑ p : Fin t, C 0 p * Ginv p q) * B q 0 := by
      simp only [Matrix.mul_apply]
    refine hmul1.trans ?_
    have hmul2 :
        ∑ q : Fin t, (∑ p : Fin t, C 0 p * Ginv p q) * B q 0 =
          ∑ q : Fin t, ∑ p : Fin t, w p * Ginv p q * w q := by
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [C, B, Finset.sum_mul]
    refine hmul2.trans ?_
    have hmul3 :
        ∑ q : Fin t, ∑ p : Fin t, w p * Ginv p q * w q =
          ∑ p : Fin t, w p * ∑ q : Fin t, Ginv p q * w q := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hre : ∑ q, w p * Ginv p q * w q = ∑ q, w p * (Ginv p q * w q) := by
        refine Finset.sum_congr rfl fun q _ => mul_assoc _ _ _
      rw [hre, ← Finset.mul_sum]
    exact hmul3.trans (by simp only [dotProduct_eq, mulVec_sum_eq])
  have hGinv : Ginv = ⅟G := rfl
  rw [hGinv] at hsub hmul
  rw [hsub, hD, hmul]

lemma trace_coeff_update {t : ℕ} (Ginv : Matrix (Fin t) (Fin t) ℝ)
    (w : Fin t → ℝ) (σ : ℝ) (hsym : Ginvᵀ = Ginv) :
    let B : Matrix (Fin t) (Fin 1) ℝ := fun p _ => w p
    let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => σ
    let C : Matrix (Fin 1) (Fin t) ℝ := fun _ q => w q
    (Ginv * B * S * C * Ginv).trace =
      σ * ((Ginv *ᵥ w) ⬝ᵥ (Ginv *ᵥ w)) := by
  intro B S C
  have hGB : ∀ p, (Ginv * B) p 0 = (Ginv *ᵥ w) p := by
    intro p
    rw [Matrix.mul_apply, mulVec, dotProduct]
  have hmid : ∀ p q, (Ginv * B * S * C) p q = σ * (Ginv *ᵥ w) p * w q := by
    intro p q
    have hS : (Ginv * B * S) p 0 = (Ginv * B) p 0 * σ := by
      rw [Matrix.mul_apply, Fin.sum_univ_one]
    have hC : (Ginv * B * S * C) p q = (Ginv * B * S) p 0 * w q := by
      rw [Matrix.mul_apply, Fin.sum_univ_one]
    rw [hC, hS, hGB]
    ring
  have hcol : ∀ q p, Ginv q p = Ginv p q := by
    intro q p
    have hentry : Ginvᵀ p q = Ginv p q := congr_fun (congr_fun hsym p) q
    simpa [Matrix.transpose_apply] using hentry
  have hdiag : ∀ p, (Ginv * B * S * C * Ginv) p p =
      σ * (Ginv *ᵥ w) p * (Ginv *ᵥ w) p := by
    intro p
    have hmul : (Ginv * B * S * C * Ginv) p p =
        ∑ q, (Ginv * B * S * C) p q * Ginv q p := by
      simp [Matrix.mul_apply]
    rw [hmul]
    have hsum : ∑ q, (Ginv * B * S * C) p q * Ginv q p =
        ∑ q, σ * (Ginv *ᵥ w) p * w q * Ginv q p := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hmid]
    rw [hsum]
    have hre : ∑ q, σ * (Ginv *ᵥ w) p * w q * Ginv q p =
        ∑ q, σ * (Ginv *ᵥ w) p * (w q * Ginv p q) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hcol q p]
      ring
    rw [hre]
    have hfac : ∑ q, σ * (Ginv *ᵥ w) p * (w q * Ginv p q) =
        σ * (Ginv *ᵥ w) p * ∑ q, w q * Ginv p q := by
      rw [← Finset.mul_sum]
    rw [hfac]
    have hdotp : ∑ q, w q * Ginv p q = (Ginv *ᵥ w) p := by
      simp [dotProduct, mulVec, mul_comm]
    rw [hdotp]
  have hsum : (Ginv * B * S * C * Ginv).trace =
      ∑ p, σ * (Ginv *ᵥ w) p * (Ginv *ᵥ w) p := by
    simp only [Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun p _ => hdiag p
  have hpull : ∑ p, σ * (Ginv *ᵥ w) p * (Ginv *ᵥ w) p =
      σ * ((Ginv *ᵥ w) ⬝ᵥ (Ginv *ᵥ w)) := by
    have hre : ∑ p, σ * (Ginv *ᵥ w) p * (Ginv *ᵥ w) p =
        ∑ p, σ * ((Ginv *ᵥ w) p * (Ginv *ᵥ w) p) := by
      refine Finset.sum_congr rfl fun p _ => mul_assoc _ _ _
    rw [hre, ← Finset.mul_sum, dotProduct]
  rw [hsum, hpull]

/-- Appending one column adds `(1 + ‖G⁻¹ Bᵀ v‖²) / residual` to the inverse trace. -/
theorem append_inv_trace_increment {k t : ℕ}
    (B : Matrix (Fin k) (Fin t) ℝ) (v : Fin k → ℝ)
    (hG : (Bᵀ * B).det ≠ 0)
    (hs : v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v))) ≠ 0) :
    (((appendColumn B v)ᵀ * appendColumn B v)⁻¹).trace =
      ((Bᵀ * B)⁻¹).trace +
        (1 + (((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) /
          (v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)))) := by
  let G := Bᵀ * B
  let w := Bᵀ *ᵥ v
  let α := v ⬝ᵥ v
  let s := α - (w ⬝ᵥ (G⁻¹ *ᵥ w))
  have hs' : s ≠ 0 := by simpa [s, α, w, G] using hs
  let M := (appendColumn B v)ᵀ * appendColumn B v
  let e : (Fin t ⊕ Fin 1) ≃ Fin (t + 1) := finSumFinEquiv
  let Bmat : Matrix (Fin t) (Fin 1) ℝ := fun p _ => w p
  let Cmat : Matrix (Fin 1) (Fin t) ℝ := fun _ q => w q
  let Dmat : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => α
  let Bord := Matrix.fromBlocks G Bmat Cmat Dmat
  have hBord : M.submatrix e e = Bord := by
    simpa [M, Bord, G, w, α, Bmat, Cmat, Dmat, e] using
      appendColumn_gram_fromBlocks B v
  letI iG : Invertible G := invertible_of_det_ne_zero G (by simpa [G] using hG)
  have hGinvOf : ⅟G = G⁻¹ := Matrix.invOf_eq_nonsing_inv G
  have hGsym : Gᵀ = G := by simp [G, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hinvsym : (G⁻¹)ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, hGsym]
  let Smat := Dmat - Cmat * ⅟G * Bmat
  have hS : Smat 0 0 = s := by
    have hentry := schur_corner G w α
    simpa [Smat, Dmat, Cmat, Bmat, s, hGinvOf] using hentry
  have hSdet : Smat.det ≠ 0 := by
    rw [Matrix.det_fin_one, hS]
    exact hs'
  letI iS : Invertible Smat := invertible_of_det_ne_zero Smat hSdet
  letI iBord : Invertible Bord := by
    simpa [Bord, Smat] using fromBlocks₁₁Invertible G Bmat Cmat Dmat
  letI iSub : Invertible (M.submatrix e e) := hBord.symm ▸ iBord
  letI iM : Invertible M := invertibleOfSubmatrixEquivInvertible M e e
  have htraceEq : (M⁻¹).trace = (Bord⁻¹).trace := by
    have hsub : ⅟(M.submatrix e e) = (⅟M).submatrix e e :=
      invOf_submatrix_equiv_eq M e e
    have hBordInv : ⅟Bord = (⅟M).submatrix e e := by simpa [hBord] using hsub
    have htr : (⅟Bord).trace = (⅟M).trace := by
      rw [hBordInv]
      exact trace_submatrix_equiv e (⅟M)
    rw [← Matrix.invOf_eq_nonsing_inv M, ← Matrix.invOf_eq_nonsing_inv Bord, htr]
  rw [htraceEq]
  have hformula := invOf_fromBlocks₁₁_eq G Bmat Cmat Dmat
  rw [← Matrix.invOf_eq_nonsing_inv Bord]
  have hBordDef : Bord = Matrix.fromBlocks G Bmat Cmat Dmat := rfl
  rw [hformula]
  have hsplit := trace_fromBlocks
      (⅟G + ⅟G * Bmat * ⅟Smat * Cmat * ⅟G)
      (-(⅟G * Bmat * ⅟Smat))
      (-(⅟Smat * Cmat * ⅟G))
      (⅟Smat)
  rw [hsplit, Matrix.trace_add]
  have hGtr : (⅟G).trace = (G⁻¹).trace := by simp [hGinvOf]
  have hSmatFun : Smat = fun _ _ : Fin 1 => s := by
    ext i j
    fin_cases i
    fin_cases j
    exact hS
  have hSentry : (⅟Smat) 0 0 = s⁻¹ := by
    have hinv := inv_fin_one_entry s hs'
    simpa [hSmatFun] using hinv
  have hStr : (⅟Smat).trace = s⁻¹ := by rw [trace_fin_one, hSentry]
  have hcorr : (⅟G * Bmat * ⅟Smat * Cmat * ⅟G).trace =
      s⁻¹ * ((G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w)) := by
    have hSinvFun : ⅟Smat = fun _ _ : Fin 1 => s⁻¹ := by
      ext i j
      fin_cases i
      fin_cases j
      -- ⅟ and ⁻¹ agree, and the entry is s⁻¹
      have hinvEq : ⅟Smat = Smat⁻¹ := Matrix.invOf_eq_nonsing_inv Smat
      rw [hinvEq]
      exact hSentry
    have hupd := trace_coeff_update (⅟G) w s⁻¹ (by simp [hGinvOf, hinvsym])
    simpa [Bmat, Cmat, hSinvFun, hGinvOf] using hupd
  rw [hGtr, hcorr, hStr]
  have hdot : (G⁻¹ *ᵥ w) ⬝ᵥ (G⁻¹ *ᵥ w) =
      ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) := by
    simp [G, w]
  rw [hdot]
  have hden : s = v ⬝ᵥ v - ((Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * B)⁻¹ *ᵥ (Bᵀ *ᵥ v))) := by
    simp [s, α, w, G]
  rw [hden]
  field_simp [hs']
  ring

end StructuredColumnSelection
