# Mathlib-facing notes

## Already reusable

Phase 2 proves a Fin-indexed Cauchy–Binet formula:

- `det_mul_eq_sum_det_submatrix_mul_prod`
- `fiberSum`
- `det_mul_cauchyBinet`
- `det_mul_cauchyBinet_powersetCard`

These are the natural candidates for a later mathlib contribution. A
type-generic version (arbitrary finite index types, not only `Fin k`
and `Fin n`) would match the in-flight mathlib PR
https://github.com/leanprover-community/mathlib4/pull/40473 more
closely. This repository does not open that PR.

Phase 1 wrappers remain:

- orthogonal-row / orthogonal-column structural predicates;
- selected square column submatrices via `submatrix`;
- selected Gram matrix product forms.

## Later candidates

- finite weighted subset identities for inverse Gram matrices;
- matrix expectation identities over explicit finite distributions.
