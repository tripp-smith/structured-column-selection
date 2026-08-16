# Mathlib-facing notes

## Already reusable

Phase 2 proves a Fin-indexed Cauchy–Binet formula:

- `det_mul_eq_sum_det_submatrix_mul_prod`
- `fiberSum`
- `det_mul_cauchyBinet`
- `det_mul_cauchyBinet_powersetCard`

Phase 3 adds a finite inverse-Gram / complementary-minor identity:

- `volumeWeightedInvGrams_sum`
- `complementaryMinor`
- double-counting of `k`-sets containing a fixed `(k-1)`-set

These are the natural candidates for a later mathlib contribution. A
type-generic Cauchy–Binet version would match the in-flight mathlib PR
https://github.com/leanprover-community/mathlib4/pull/40473 more
closely. This repository does not open that PR.

The `powersetCard` statement is now also exported as `cauchyBinet`,
together with `det_mul_eq_zero_of_rank_deficient`, so it can be
compared line-for-line with
[AlgebraicCombinatorics.CauchyBinet](https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/CauchyBinet.html)
(`faabian/algebraic-combinatorics`). That file uses the same
`colsSubmatrix` / `rowsSubmatrix` constructors
(`A.submatrix id (S.orderEmbOfFin h)` and the row dual) and the same
vacuous `dite` on cardinality. This repository does not import that
project.

Phase 1 wrappers remain:

- orthogonal-row / orthogonal-column structural predicates;
- selected square column submatrices via `submatrix`;
- selected Gram matrix product forms.

Phase 4 adds a finite weighted Markov inequality and the trace form
of the inverse-Gram identity:

- `invFrobWeight`
- `expectedInvFrobSq`
- `weightedMarkov`
- `markovInvFrob`

These stay on `Finset` sums and do not introduce measure theory.

Phase 5 adds structural CPQR lemmas that stay on finite Gram
determinants and matrix rank:

- `leverageSum`
- `firstPivot_is_max`
- `firstLeverage_ge`
- `cpqrSet_card_eq`
- `cpqr_k1_volume_ge`
- `residualEnergy`
- `nextResidual_ge`
- `cpqr_volume_ge_binomial`
- `mulVec_energy_le`, `col_energy_le`, `lastResidual_ge`
- residual nonnegativity and unused-column span control

These use mathlib `Matrix.rank`, `rank_transpose_mul_self`,
`rank_of_det_ne_zero`, `det_fromBlocks₁₁`, and `det_submatrix_equiv_self`.
The `k=1` volume bound is a determinant comparison, not a
spectral-norm argument. The binomial volume bound is a product of
Gram-determinant ratios and is not polynomial in `n` and `k`.

Phase 6 adds the triangular inverse machinery behind
`pivotGram_inv_trace_le`:

- `geom_sum_one_sub` (finite geometric series with `1 - X` in a
  noncommutative matrix ring)
- unit-triangular inversion by the finite Neumann series
  `S = Σ_{p<k} (1-U)^p` (`gsS_mul_gsU`, `gsU_inv`)
- the Businger–Golub entry bound `|S i j| ≤ 2^{j-i-1}` for the
  inverse of a unit upper triangular matrix with `|U i j| ≤ 1`
  (`gsS_entry_abs_le`)
- the trace factorization `tr((UᵀΔU)⁻¹) = Σ_l δ_l⁻¹ ‖S e_l‖²`
  (`pivotGram_inv_trace`)

The generic triangular-inverse lemmas are mathlib-shaped candidates;
the CPQR-specific ones stay here. The `frame38` witness theorems use
`native_decide` and are not mathlib candidates.

Phase 7 adds residual monotonicity, the leave-one-out inverse-trace
identity, and row-orthonormality of the implicit CPQR factor:

- `residualSq_antitone`, `residualSq_insert_downdate`
- `selectedColGram_inv_trace_eq_sum_inv_residual`
- `selectedCols_energy_mul_inv_trace_ge`
- `gsR_mul_transpose`

These stay on finite Gram projectors and are not a joint
`poly(n,k)` inverse-norm theorem. The bidiagonal-`U` bound
`pivotGram_inv_trace_le_of_bidiagonal` is a hypothesis on the
coefficient pattern of `U`, not a class of `A`.

Phase 8 adds the binomial inverse-energy comparison and the Path 3
complementary-dimension class:

- `selectedColGram_inv_trace_le_card_div_det`
- `cpqr_inv_energy_le_choose`
- `cpqr_inv_energy_le_of_minDim`

The first two are finite Gram / binomial identities. The third
restricts the shape of `A` (`min(k, n-k) ≤ d`) and is not a
universal `poly(n,k)` theorem.

The §8 census, including the Wave 1 ETF / clustered / Haar-growth
tracks, the Path 2 adverse ladder, and the static-class diagnostics
in `experiments/census_static_class_seed1.json`, is Python-only and
is not a mathlib candidate.

## Later candidates

- a type-generic version of `weightedMarkov` for mathlib;
- operator-norm comparisons packaged with the existing Frobenius proxy.
