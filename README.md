# structured-column-selection

Lean 4 formalization and computational study of quasi-optimal RRQR/CSSP
under orthogonal-row structure (`A Aᵀ = I`) for Simons Workshop Problem 4.1.

## Status

Machine-checked randomized quasi-optimal column selection for the
orthogonal-row case of Simons Problem 4.1.

Phases completed:

- Milestone A (structural foundations)
  - `milestoneA_transpose_correspondence`
  - `milestoneA_selectedSquare_entry`
  - `milestoneA_selectedGram_formula`
- Milestone B (volume normalisation)
  - `milestoneB_cauchyBinet`
  - `milestoneB_volume_normalization`
- Milestone C (exact inverse-Gram identity)
  - `milestoneC_adjugate_sum`
  - `milestoneC_inverse_gram_expectation`
- Milestone D (finite inverse-Frobenius expectation and Markov tail)
  - `milestoneD_expected_inv_frob_sq`
  - `milestoneD_markov_inv_frob`

- Milestone E discovery layer (CPQR algorithm, not a bound)
  - `milestoneE_residual_empty`
  - `milestoneE_cpqr_card_le`
  - `milestoneE_cpqr_frame23`

Not yet claimed:

- a polynomial CPQR theorem, counterexample, or refined structural class
- CSSP perturbation bridge
- a solution of all of Problem 4.1

The formal Milestone C statement uses adjugates. That is the correct
finite identity: `det(A_J)² (A_J A_Jᵀ)⁻¹` agrees with
`adj(A_J A_Jᵀ)` on invertible blocks, and the adjugate supplies the
singular summands that the naive inverse (zero when singular) would
drop.

## Lean module map

- `StructuredColumnSelection/Definitions.lean`:
  structural predicates and projector definition.
- `StructuredColumnSelection/PrincipalColumns.lean`:
  selected-column square/Gram definitions and foundational identities.
- `StructuredColumnSelection/OrthogonalRows.lean`:
  transpose correspondence theorems.
- `StructuredColumnSelection/CauchyBinet.lean`:
  finite Cauchy–Binet for rectangular products.
- `StructuredColumnSelection/VolumeWeights.lean`:
  squared-minor weights and their normalisation.
- `StructuredColumnSelection/InverseGramExpectation.lean`:
  adjugate form of the inverse-Gram sum.
- `StructuredColumnSelection/InverseNormBounds.lean`:
  volume-weighted inverse-Frobenius energy and a finite Markov tail.
- `StructuredColumnSelection/ColumnPivotedQR.lean`:
  greedy CPQR residuals, pivots, and selected sets.
- `StructuredColumnSelection/SmallInstanceChecks.lean`:
  exact rational enumerations used as independent witnesses.
- `StructuredColumnSelection/Theorems.lean`:
  public theorem exports.

## Cloud Agent environment

The repository ships a minimal Cloud Agent setup in
`.cursor/environment.json` that runs `.cursor/install.sh`, which installs
Lean tooling idempotently, fetches mathlib cache, and builds the project.

## Skill cadence

Phase execution cadence is defined in:

- `.cursor/skills/phase-cadence/SKILL.md`

It covers specify → implement → verify → document → ship, with explicit
claim discipline.
