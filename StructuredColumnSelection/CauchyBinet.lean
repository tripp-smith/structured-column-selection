import StructuredColumnSelection.PrincipalColumns

/-!
# Cauchy–Binet

Finite Cauchy–Binet for rectangular products `A : k×n` and `B : n×k`.
The proof expands `det (A * B)` over all index maps `g : Fin k → Fin n`,
discards non-injective maps (repeated columns), and groups the rest by
image. A linear order on `Fin n` is used only to name each minor via
`orderEmbOfFin`.
-/

namespace StructuredColumnSelection

open Matrix Equiv Equiv.Perm Finset Function

variable {R : Type*} [CommRing R]

/-- Column square selected by an increasing enumeration of `J`. -/
def colsSubmatrix {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (J : Finset (Fin n)) (h : J.card = k) : Matrix (Fin k) (Fin k) R :=
  A.submatrix id (J.orderEmbOfFin h)

/-- Row square selected by an increasing enumeration of `J`. -/
def rowsSubmatrix {k n : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (J : Finset (Fin n)) (h : J.card = k) : Matrix (Fin k) (Fin k) R :=
  B.submatrix (J.orderEmbOfFin h) id

@[simp]
theorem colsSubmatrix_eq_selectedSquare {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (J : Finset (Fin n)) (h : J.card = k) :
    colsSubmatrix A J h = SelectedSquare A (J.orderEmbOfFin h) :=
  rfl

/-- Leibniz expansion of `det (A * B)` over all column-index maps. -/
theorem det_mul_eq_sum_det_submatrix_mul_prod {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ g : Fin k → Fin n, (A.submatrix id g).det * ∏ i, B (g i) i := by
  conv_lhs => rw [det_apply']
  simp_rw [mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

/-- Relabelling a fixed column list `φ` by permutations reconstructs the
product of the two minors. -/
theorem fiberSum {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (φ : Fin k → Fin n) :
    ∑ π : Perm (Fin k),
        (A.submatrix id fun j => φ (π j)).det * ∏ i, B (φ (π i)) i =
      (A.submatrix id φ).det * (B.submatrix φ id).det := by
  have hA : ∀ π : Perm (Fin k),
      (A.submatrix id fun j => φ (π j)).det =
        (A.submatrix id φ).submatrix id π |>.det := by
    intro π
    congr
    ext i j
    simp [submatrix_apply]
  simp_rw [hA, det_permute']
  rw [det_apply' (B.submatrix φ id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [submatrix_apply, id_eq]
  ring

lemma card_image_univ {k n : ℕ} {g : Fin k → Fin n} (hg : Injective g) :
    (image g univ).card = k := by
  rw [card_image_of_injective _ hg, card_univ, Fintype.card_fin]

/-- Permutation recovering an injective map from the sorted enumeration of
its image. -/
noncomputable def imagePerm {k n : ℕ} {g : Fin k → Fin n} (hg : Injective g) :
    Perm (Fin k) :=
  Equiv.ofBijective
    (fun a =>
      ((image g univ).orderIsoOfFin (card_image_univ hg)).symm
        ⟨g a, mem_image_of_mem g (mem_univ a)⟩)
    (Injective.bijective_of_finite (by
      intro a b hab
      have h :=
        ((image g univ).orderIsoOfFin (card_image_univ hg)).symm.injective hab
      exact hg (Subtype.ext_iff.mp h)))

lemma imagePerm_spec {k n : ℕ} {g : Fin k → Fin n} (hg : Injective g)
    (j : Fin k) :
    (image g univ).orderEmbOfFin (card_image_univ hg) (imagePerm hg j) = g j := by
  rw [← coe_orderIsoOfFin_apply]
  simp [imagePerm]

lemma image_comp_orderEmb {k n : ℕ} (S : Finset (Fin n)) (hS : S.card = k)
    (π : Perm (Fin k)) :
    image (fun j => S.orderEmbOfFin hS (π j)) univ = S := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨_, rfl⟩
    exact S.orderEmbOfFin_mem hS _
  · intro hx
    have hx' : x ∈ image (S.orderEmbOfFin hS) univ := by
      rw [image_orderEmbOfFin_univ]
      exact hx
    obtain ⟨a, ha⟩ := mem_image.mp hx'
    exact ⟨π.symm a, by simp [ha]⟩

/-- **Cauchy–Binet.** The determinant of a rectangular product is the sum of
products of complementary maximal minors, indexed by `k`-subsets. -/
theorem det_mul_cauchyBinet {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ S : { s : Finset (Fin n) // s.card = k },
        (colsSubmatrix A S.1 S.2).det * (rowsSubmatrix B S.1 S.2).det := by
  classical
  rw [det_mul_eq_sum_det_submatrix_mul_prod]
  have hvanish : ∀ g : Fin k → Fin n, ¬ Injective g →
      (A.submatrix id g).det * ∏ i, B (g i) i = 0 := by
    intro g hg
    rw [not_injective_iff] at hg
    obtain ⟨a, b, hab, hne⟩ := hg
    rw [det_zero_of_column_eq hne (fun _ => by simp [submatrix_apply, hab]),
      zero_mul]
  have hfilter :
      ∑ g : Fin k → Fin n, (A.submatrix id g).det * ∏ i, B (g i) i =
        ∑ g ∈ univ.filter Injective,
          (A.submatrix id g).det * ∏ i, B (g i) i := by
    refine (sum_subset (filter_subset _ _) ?_).symm
    intro g _ hg
    exact hvanish g (by simpa [mem_filter] using hg)
  rw [hfilter]
  have hfiber :
      ∑ S : { s : Finset (Fin n) // s.card = k },
          (colsSubmatrix A S.1 S.2).det * (rowsSubmatrix B S.1 S.2).det =
        ∑ S : { s : Finset (Fin n) // s.card = k },
          ∑ π : Perm (Fin k),
            (A.submatrix id fun j => S.1.orderEmbOfFin S.2 (π j)).det *
              ∏ i, B (S.1.orderEmbOfFin S.2 (π i)) i := by
    refine Fintype.sum_congr _ _ fun S => ?_
    simpa [colsSubmatrix, rowsSubmatrix] using (fiberSum A B (S.1.orderEmbOfFin S.2)).symm
  rw [hfiber, ← Fintype.sum_sigma']
  refine (Finset.sum_bij
      (fun p _ => fun j => p.1.1.orderEmbOfFin p.1.2 (p.2 j))
      ?hi ?inj ?surj ?eq).symm
  · intro p _
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro a b hab
    exact p.2.injective ((p.1.1.orderEmbOfFin p.1.2).injective hab)
  · rintro ⟨⟨S1, hS1⟩, π1⟩ _ ⟨⟨S2, hS2⟩, π2⟩ _ heq
    have hSeq : S1 = S2 := by
      rw [← image_comp_orderEmb S1 hS1 π1, ← image_comp_orderEmb S2 hS2 π2, heq]
    subst hSeq
    have hπ : π1 = π2 := by
      refine Equiv.ext fun a => ?_
      have h3 := congrFun heq a
      exact Fin.ext
        ((orderEmbOfFin_eq_orderEmbOfFin_iff (h := hS1) (h' := hS2)).mp h3)
    subst hπ
    rfl
  · intro g hg
    rw [mem_filter] at hg
    refine ⟨⟨⟨image g univ, card_image_univ hg.2⟩, imagePerm hg.2⟩, mem_univ _, ?_⟩
    funext j
    exact imagePerm_spec hg.2 j
  · intro _ _
    rfl

/-- Cauchy–Binet indexed by `powersetCard`, with a vacuous `dite` on cardinality. -/
theorem det_mul_cauchyBinet_powersetCard {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
        if h : J.card = k then
          (colsSubmatrix A J h).det * (rowsSubmatrix B J h).det
        else 0 := by
  rw [det_mul_cauchyBinet]
  refine Finset.sum_bij'
      (fun S _ => S.1)
      (fun J hJ => ⟨J, (mem_powersetCard.mp hJ).2⟩)
      (fun S _ => mem_powersetCard.mpr ⟨subset_univ _, S.2⟩)
      (fun _ _ => mem_univ _)
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun S _ => dif_pos S.2)

end StructuredColumnSelection
