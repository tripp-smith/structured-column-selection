# Application layer status

Phase 3 adds an independent inverse-Gram adjugate check. The full
`structselect` selector API from `SPEC.md` is still not implemented.

`tests/test_volume_normalization.py` enumerates squared maximal minors
for two rational orthogonal-row frames.

`tests/test_inverse_gram.py` enumerates `adj(A_J A_Jᵀ)` on the same
`2×3` frame and checks that the matrices sum to `2 I`. That calculation
is a diagnostic witness for Milestone C; the source of truth is
`milestoneC_inverse_gram_expectation`.

When selectors are added, this document will separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.
