# Mathlib-facing notes

Phase 1 introduces reusable wrappers around standard `Matrix` constructions:

- orthogonal-row / orthogonal-column structural predicates;
- selected square column submatrices via `submatrix`;
- selected Gram matrix product forms.

Potentially reusable upstream patterns in later phases:

- finite weighted subset identities for determinant squares;
- matrix expectation identities over explicit finite distributions.

No upstream proposal is prepared yet; this file tracks candidates as the
theory deepens.
