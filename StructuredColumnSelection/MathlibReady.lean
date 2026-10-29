import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.VolumeWeights

/-!
Potentially reusable declarations are checked here for later upstream
evaluation. Presence in this module is not a claim that a mathlib pull
request exists.

- `det_mul_cauchyBinet`
- `det_mul_cauchyBinet_powersetCard`
- `cauchyBinet`
- `volumeWeights_sum_eq_one`
- `weightedMarkov`
- `markovInvFrob`
-/

namespace StructuredColumnSelection

open Classical
open Finset
open scoped BigOperators Matrix

example {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ S : { s : Finset (Fin n) // s.card = k },
        (colsSubmatrix A S.1 S.2).det * (rowsSubmatrix B S.1 S.2).det :=
  det_mul_cauchyBinet A B

example {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
        if h : J.card = k then
          (colsSubmatrix A J h).det * (rowsSubmatrix B J h).det
        else 0 :=
  det_mul_cauchyBinet_powersetCard A B

example {k n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
        if h : J.card = k then
          (colsSubmatrix A J h).det * (rowsSubmatrix B J h).det
        else 0 :=
  cauchyBinet A B

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard k, volumeWeight A J = 1 :=
  volumeWeights_sum_eq_one A hA

example {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) {t : ℝ} (ht : 0 < t) :
    ∑ i ∈ s.filter (fun i => w i * t < x i), w i ≤ t⁻¹ * ∑ i ∈ s, x i :=
  weightedMarkov s w x hw hx ht

example {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (hA : OrthogonalRows A)
    {δ : ℝ} (hδ : 0 < δ) :
    ∑ J ∈ ((univ : Finset (Fin n)).powersetCard k).filter
        (invFrobExceeds A (((k : ℝ) * ((n + 1 - k : ℕ) : ℝ)) / δ)),
      volumeWeight A J ≤ δ :=
  markovInvFrob A hA hδ

end StructuredColumnSelection
