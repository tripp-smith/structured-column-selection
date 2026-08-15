# structured-column-selection

Lean 4 formalization and computational study of quasi-optimal RRQR/CSSP
under orthogonal-row structure (`A Aᵀ = I`) for Simons Workshop Problem 4.1.

## Status

Phase 1 (Milestone A: structural foundations) is implemented.

- `milestoneA_transpose_correspondence`:
  formalizes `A Aᵀ = I` for `A = Qᵀ` iff `Qᵀ Q = I`.
- `milestoneA_selectedSquare_entry` and
  `milestoneA_selectedGram_formula`:
  establish core selected-column and Gram identities used by later
  volume-sampling proofs.

Not yet claimed:

- Milestone B (`∑ det(A_J)^2 = 1`)
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
- `StructuredColumnSelection/Theorems.lean`:
  public Phase 1 theorem exports.

## Cloud Agent environment

The repository ships a minimal Cloud Agent setup in
`.cursor/environment.json` that runs `.cursor/install.sh`, which installs
Lean tooling idempotently, fetches mathlib cache, and builds the project.

## Skill cadence

Phase execution cadence is defined in:

- `.cursor/skills/phase-cadence/SKILL.md`

It covers specify → implement → verify → document → ship, with explicit
claim discipline.
