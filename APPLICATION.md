# Application layer status

Phase 5 adds a Python CPQR selector in `structselect/cpqr.py` that
uses the same Gram-determinant residual as Lean. It is a discovery
witness, not a certified polynomial bound.

`tests/test_volume_normalization.py` enumerates squared maximal minors
for two rational orthogonal-row frames.

`tests/test_inverse_gram.py` enumerates `adj(A_J A_Jᵀ)` on the same
`2×3` frame and checks that the matrices sum to `2 I`. That calculation
is a diagnostic witness for Milestone C; the source of truth is
`milestoneC_inverse_gram_expectation`.

`tests/test_inverse_norm.py` enumerates `tr(adj(A_J A_Jᵀ))` on the
same `2×3` frame and checks that the traces sum to `4 = 2·(3-2+1)`.
That calculation is a diagnostic witness for Milestone D; the source
of truth is `milestoneD_expected_inv_frob_sq`.

`tests/test_cpqr.py` checks that CPQR on the `2×3` frame selects
`{0,2}` with `r_CPQR = 5/8`. The source of truth for the selected
set is `milestoneE_cpqr_frame23`.

When selectors are added, this document will separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.
