# structured-column-selection

Lean 4 formalization and computational study of quasi-optimal RRQR/CSSP
under orthogonal-row structure (`A Aᵀ = I`) for Simons Workshop Problem 4.1.

## Status

Investigating Simons Problem 4.1 for orthogonal-row matrices.

Phases completed:

- Milestone A (structural foundations)
  - `milestoneA_transpose_correspondence`
  - `milestoneA_selectedSquare_entry`
  - `milestoneA_selectedGram_formula`
- Milestone B (volume normalisation)
  - `milestoneB_cauchyBinet`
  - `milestoneB_volume_normalization`

Not yet claimed:

- Milestone C (exact inverse-Gram expectation identity)
- Milestone D randomized high-probability RRQR bound
- CPQR theorem/counterexample outcomes

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
