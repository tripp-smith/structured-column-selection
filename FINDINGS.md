# Findings

## Phase 1 (Milestone A) delivered

This phase proves the structural translation that underpins the project:
working with a `k × n` matrix `A` satisfying `A Aᵀ = I` is equivalent to
working with `Q := Aᵀ` satisfying `Qᵀ Q = I`.

It also introduces Lean definitions for selected `k × k` column blocks and
their Gram matrices, with entrywise/product identities needed in later
volume-sampling proofs.

## What remains open

The phase does **not** prove the volume normalization, inverse-Gram
expectation, or randomized high-probability guarantees yet.
Those belong to Milestones B-D in `SPEC.md`.
