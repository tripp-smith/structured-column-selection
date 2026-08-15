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

## Later candidates

- a type-generic version of `weightedMarkov` for mathlib;
- operator-norm comparisons packaged with the existing Frobenius proxy.
