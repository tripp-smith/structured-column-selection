import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! SPEC §11 coefficient reconstruction for a supplied orthonormal factor. -/
namespace StructuredColumnSelection
open Matrix Finset WithLp
open scoped Matrix.Norms.L2Operator

/-- Euclidean operator norm. -/
noncomputable def spectralNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖

/-- Entrywise Euclidean norm. -/
noncomputable def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

def colEmbed {n k : ℕ} (e : Fin k ↪ Fin n) : Matrix (Fin n) (Fin k) ℝ :=
  fun i j => if i = e j then 1 else 0

lemma colEmbed_mul_apply {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (e : Fin k ↪ Fin n) (i : Fin m) (j : Fin k) :
    (A * colEmbed e) i j = A i (e j) := by
  simp only [Matrix.mul_apply, colEmbed]
  rw [Finset.sum_eq_single (e j)]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact (h (mem_univ _)).elim

lemma colEmbed_orth {n k : ℕ} (e : Fin k ↪ Fin n) :
    (colEmbed e)ᵀ * colEmbed e = 1 := by
  ext j j'
  simp only [Matrix.mul_apply, transpose_apply, colEmbed, one_apply]
  by_cases hjj : j = j'
  · subst hjj
    rw [Finset.sum_eq_single (e j)]
    · simp
    · intro t _ ht
      simp [ht]
    · intro h
      exact (h (mem_univ _)).elim
  · have hne : e j ≠ e j' := fun h => hjj (e.injective h)
    rw [if_neg hjj]
    apply Finset.sum_eq_zero
    intro t _
    by_cases htj : t = e j
    · simp [htj, hne]
    · simp [htj]

lemma real_conjTranspose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Aᴴ = Aᵀ := by
  ext i j
  simp [conjTranspose_apply]

lemma spectralNorm_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    spectralNorm Aᵀ = spectralNorm A := by
  unfold spectralNorm
  rw [← real_conjTranspose, l2_opNorm_conjTranspose]

lemma spectralNorm_mul_le {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ) :
    spectralNorm (A * B) ≤ spectralNorm A * spectralNorm B := by
  simpa [spectralNorm] using l2_opNorm_mul A B

lemma spectralNorm_sub_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    spectralNorm (A - B) ≤ spectralNorm A + spectralNorm B := by
  simpa [spectralNorm] using norm_sub_le A B

lemma euclid_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    ‖(toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [pow_two]

lemma dot_sq {n : ℕ} (v : Fin n → ℝ) : v ⬝ᵥ v = ∑ i, v i ^ 2 := by
  simp [dotProduct, pow_two]

lemma spectralNorm_isometry_le {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Qᵀ * Q = 1) : spectralNorm Q ≤ 1 := by
  unfold spectralNorm
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [LinearEquiv.trans_apply, one_mul]
  have happ :
      (toEuclideanLin Q).toContinuousLinearMap x =
        toLp 2 (Q *ᵥ ofLp x) := by
    change toEuclideanLin Q x = _
    simpa using toEuclideanLin_toLp Q (ofLp x)
  rw [happ]
  have hv : ofLp x ⬝ᵥ ofLp x = ‖x‖ ^ 2 := by
    rw [dot_sq, ← euclid_norm_sq]
  have hsq :
      ‖(toLp 2 (Q *ᵥ ofLp x) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [euclid_norm_sq, ← dot_sq, dotProduct_mulVec, ← mulVec_transpose,
      mulVec_mulVec, hQ, one_mulVec, hv]
  have hnn :
      0 ≤ ‖(toLp 2 (Q *ᵥ ofLp x) : EuclideanSpace ℝ (Fin n))‖ := norm_nonneg _
  exact le_of_eq ((sq_eq_sq₀ hnn (norm_nonneg _)).1 hsq)

lemma spectralNorm_cols_le {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (e : Fin k ↪ Fin n) :
    spectralNorm (A * colEmbed e) ≤ spectralNorm A := by
  have hP := spectralNorm_isometry_le (colEmbed e) (colEmbed_orth e)
  exact (spectralNorm_mul_le A (colEmbed e)).trans (mul_le_of_le_one_right
    (by unfold spectralNorm; exact norm_nonneg _) hP)

lemma rowSubmatrix_transpose {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (e : Fin k ↪ Fin n) :
    Qᵀ * colEmbed e = (Q.submatrix e id)ᵀ := by
  ext a b
  rw [colEmbed_mul_apply]
  simp [submatrix_apply, transpose_apply]

lemma factor_reconstruction {m n k : ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (e : Fin k ↪ Fin n)
    (hU : IsUnit ((Q.submatrix e id)ᵀ).det) :
    (U * S * Qᵀ * colEmbed e) * ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ = U * S * Qᵀ := by
  rw [Matrix.mul_assoc (U * S) Qᵀ (colEmbed e), rowSubmatrix_transpose]
  have hmul : (Q.submatrix e id)ᵀ * ((Q.submatrix e id)ᵀ)⁻¹ = 1 :=
    mul_nonsing_inv ((Q.submatrix e id)ᵀ) hU
  calc
    (U * S * (Q.submatrix e id)ᵀ) * ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ
        = U * S * (((Q.submatrix e id)ᵀ) * ((Q.submatrix e id)ᵀ)⁻¹) * Qᵀ := by
          simp [Matrix.mul_assoc]
    _ = U * S * Qᵀ := by
          rw [hmul]
          simp [Matrix.mul_assoc]

lemma residual_identity {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (e : Fin k ↪ Fin n)
    (hA : A = U * S * Qᵀ + E)
    (hU : IsUnit ((Q.submatrix e id)ᵀ).det) :
    A - (A * colEmbed e) * (((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ) =
      E - (E * colEmbed e) * (((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ) := by
  set T : Matrix (Fin k) (Fin n) ℝ := ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ
  have hB := factor_reconstruction U S Q e hU
  have hsplit : A * colEmbed e = (U * S * Qᵀ) * colEmbed e + E * colEmbed e := by
    rw [hA, Matrix.add_mul]
  rw [hsplit, Matrix.add_mul, hA]
  have hassoc : ((U * S * Qᵀ) * colEmbed e) * T =
      (U * S * Qᵀ * colEmbed e) * ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ := by
    simp [T, Matrix.mul_assoc]
  rw [hassoc, hB]
  abel

lemma spectral_inv_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    spectralNorm (Mᵀ)⁻¹ = spectralNorm M⁻¹ := by
  rw [← transpose_nonsing_inv, spectralNorm_transpose]

lemma spectralNorm_coeff_le {n k : ℕ} (Q : Matrix (Fin n) (Fin k) ℝ)
    (hQ : Qᵀ * Q = 1) (e : Fin k ↪ Fin n) :
    spectralNorm (((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ) ≤
      spectralNorm (Q.submatrix e id)⁻¹ := by
  have hT := spectralNorm_transpose Q
  have hQle : spectralNorm Qᵀ ≤ 1 := by
    rw [hT]
    exact spectralNorm_isometry_le Q hQ
  have hinv := spectral_inv_transpose (Q.submatrix e id)
  calc
    spectralNorm (((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ)
        ≤ spectralNorm ((Q.submatrix e id)ᵀ)⁻¹ * spectralNorm Qᵀ :=
          spectralNorm_mul_le _ _
    _ ≤ spectralNorm (Q.submatrix e id)⁻¹ * 1 := by
          rw [hinv]
          gcongr
          unfold spectralNorm
          exact norm_nonneg _
    _ = spectralNorm (Q.submatrix e id)⁻¹ := by ring

/-- Spectral form of the SPEC §11 comparison. -/
theorem cssp_spectral {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    spectralNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        spectralNorm E := by
  set e : Fin k ↪ Fin n := (J.orderEmbOfFin hJ).toEmbedding
  have hdet : IsUnit ((Q.submatrix e id)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact hInv
  rw [residual_identity A E U S Q e hA hdet]
  set T : Matrix (Fin k) (Fin n) ℝ := ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ
  have hT := spectralNorm_coeff_le Q hQ e
  have hcols := spectralNorm_cols_le E e
  calc
    spectralNorm (E - (E * colEmbed e) * T)
        ≤ spectralNorm E + spectralNorm ((E * colEmbed e) * T) := spectralNorm_sub_le _ _
    _ ≤ spectralNorm E + spectralNorm (E * colEmbed e) * spectralNorm T :=
          add_le_add le_rfl (spectralNorm_mul_le _ _)
    _ ≤ spectralNorm E + spectralNorm E * spectralNorm (Q.submatrix e id)⁻¹ := by
          refine add_le_add le_rfl (mul_le_mul hcols (by simpa [T] using hT)
            (by unfold spectralNorm; exact norm_nonneg _)
            (by unfold spectralNorm; exact norm_nonneg _))
    _ = (1 + spectralNorm (Q.submatrix e id)⁻¹) * spectralNorm E := by ring

noncomputable def entryLp {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  toLp 2 fun p => A p.1 p.2

lemma frobeniusNorm_eq_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A = ‖entryLp A‖ := by
  unfold frobeniusNorm entryLp
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  exact (Fintype.sum_prod_type' fun i j => A i j ^ 2).symm

lemma frobenius_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold frobeniusNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma frobeniusNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := by
  rw [frobeniusNorm_eq_entry]
  exact norm_nonneg _

lemma frobeniusNorm_sub_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm (A - B) ≤ frobeniusNorm A + frobeniusNorm B := by
  rw [frobeniusNorm_eq_entry, frobeniusNorm_eq_entry, frobeniusNorm_eq_entry]
  have hsub : entryLp (A - B) = entryLp A - entryLp B := by
    ext p
    simp [entryLp]
  rw [hsub]
  exact norm_sub_le _ _

lemma spectral_mulVec_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    ‖(toLp 2 (A *ᵥ v) : EuclideanSpace ℝ (Fin m))‖ ≤
      spectralNorm A * ‖(toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  unfold spectralNorm
  rw [l2_opNorm_def]
  have h := ((toEuclideanLin A).toContinuousLinearMap).le_opNorm (toLp 2 v)
  simpa [LinearEquiv.trans_apply, toEuclideanLin_toLp] using h

lemma frobenius_cols_le {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (e : Fin k ↪ Fin n) :
    frobeniusNorm (A * colEmbed e) ≤ frobeniusNorm A := by
  have hnn : 0 ≤ frobeniusNorm (A * colEmbed e) := frobeniusNorm_nonneg _
  have hA : 0 ≤ frobeniusNorm A := frobeniusNorm_nonneg _
  rw [← sq_le_sq₀ hnn hA, frobenius_sq, frobenius_sq]
  refine Finset.sum_le_sum ?_
  intro i _
  have hrow : ∑ j : Fin k, (A i (e j)) ^ 2 ≤ ∑ t : Fin n, (A i t) ^ 2 := by
    have hinj : Function.Injective fun j : Fin k => e j := e.injective
    rw [← Finset.sum_image (f := fun t : Fin n => (A i t) ^ 2) (g := e) (s := univ)
      (fun _ _ _ _ h => hinj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
  simpa [colEmbed_mul_apply] using hrow

lemma frobenius_mul_spectral_le {m k n : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (B : Matrix (Fin k) (Fin n) ℝ) :
    frobeniusNorm (A * B) ≤ frobeniusNorm A * spectralNorm B := by
  have hnn : 0 ≤ frobeniusNorm (A * B) := frobeniusNorm_nonneg _
  have hright : 0 ≤ frobeniusNorm A * spectralNorm B :=
    mul_nonneg (frobeniusNorm_nonneg _) (by unfold spectralNorm; exact norm_nonneg _)
  rw [← sq_le_sq₀ hnn hright, frobenius_sq, mul_pow, frobenius_sq]
  have hrows : ∀ i, ∑ j, (A * B) i j ^ 2 ≤
      spectralNorm B ^ 2 * ∑ j, A i j ^ 2 := by
    intro i
    have hvec : ∑ j, (A * B) i j ^ 2 =
        ‖(toLp 2 ((A * B) i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      rw [euclid_norm_sq]
    rw [hvec]
    have hrow : (A * B) i = Bᵀ *ᵥ A i := by
      ext j
      simp [Matrix.mul_apply, mulVec, dotProduct, transpose_apply, mul_comm]
    rw [hrow]
    have hle := spectral_mulVec_le Bᵀ (A i)
    have hBT : spectralNorm Bᵀ = spectralNorm B := spectralNorm_transpose B
    have hrowSq : ∑ j, (A i j) ^ 2 =
        ‖(toLp 2 (A i) : EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
      rw [euclid_norm_sq]
    calc
      ‖(toLp 2 (Bᵀ *ᵥ A i) : EuclideanSpace ℝ (Fin n))‖ ^ 2
          ≤ (spectralNorm Bᵀ * ‖(toLp 2 (A i) : EuclideanSpace ℝ (Fin k))‖) ^ 2 := by
            rw [sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (by unfold spectralNorm; exact norm_nonneg _) (norm_nonneg _))]
            exact hle
      _ = spectralNorm B ^ 2 * ∑ j, A i j ^ 2 := by
            rw [hBT, mul_pow, hrowSq]
  calc
    ∑ i, ∑ j, (A * B) i j ^ 2
        ≤ ∑ i, spectralNorm B ^ 2 * ∑ j, A i j ^ 2 := Finset.sum_le_sum fun i _ => hrows i
    _ = spectralNorm B ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
          rw [← Finset.mul_sum]
    _ = (∑ i, ∑ j, A i j ^ 2) * spectralNorm B ^ 2 := by
          rw [mul_comm]

/-- Frobenius form of the SPEC §11 comparison. The coefficient is still spectral. -/
theorem cssp_frobenius {m n k : ℕ}
    (A E : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (S : Matrix (Fin k) (Fin k) ℝ)
    (Q : Matrix (Fin n) (Fin k) ℝ) (hQ : Qᵀ * Q = 1)
    (J : Finset (Fin n)) (hJ : J.card = k)
    (hInv : IsUnit (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id).det)
    (hA : A = U * S * Qᵀ + E) :
    frobeniusNorm (A - (A * colEmbed (J.orderEmbOfFin hJ).toEmbedding) *
        (((Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)ᵀ)⁻¹ * Qᵀ)) ≤
      (1 + spectralNorm (Q.submatrix (J.orderEmbOfFin hJ).toEmbedding id)⁻¹) *
        frobeniusNorm E := by
  set e : Fin k ↪ Fin n := (J.orderEmbOfFin hJ).toEmbedding
  have hdet : IsUnit ((Q.submatrix e id)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact hInv
  rw [residual_identity A E U S Q e hA hdet]
  set T : Matrix (Fin k) (Fin n) ℝ := ((Q.submatrix e id)ᵀ)⁻¹ * Qᵀ
  have hT := spectralNorm_coeff_le Q hQ e
  have hcols := frobenius_cols_le E e
  calc
    frobeniusNorm (E - (E * colEmbed e) * T)
        ≤ frobeniusNorm E + frobeniusNorm ((E * colEmbed e) * T) := frobeniusNorm_sub_le _ _
    _ ≤ frobeniusNorm E + frobeniusNorm (E * colEmbed e) * spectralNorm T :=
          add_le_add le_rfl (frobenius_mul_spectral_le _ _)
    _ ≤ frobeniusNorm E + frobeniusNorm E * spectralNorm (Q.submatrix e id)⁻¹ := by
          refine add_le_add le_rfl (mul_le_mul hcols (by simpa [T] using hT)
            (by unfold spectralNorm; exact norm_nonneg _) (frobeniusNorm_nonneg _))
    _ = (1 + spectralNorm (Q.submatrix e id)⁻¹) * frobeniusNorm E := by ring
