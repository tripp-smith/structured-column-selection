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
- residual nonnegativity and unused-column span control

These use mathlib `Matrix.rank`, `rank_transpose_mul_self`,
`rank_of_det_ne_zero`, `det_fromBlocks₁₁`, and `det_submatrix_equiv_self`.
The `k=1` volume bound is a determinant comparison, not a
spectral-norm argument. The binomial volume bound is a product of
Gram-determinant ratios and is not polynomial in `n` and `k`.

The §8 census is Python-only and is not a mathlib candidate.

## Later candidates

- a type-generic version of `weightedMarkov` for mathlib;
- operator-norm comparisons packaged with the existing Frobenius proxy.
