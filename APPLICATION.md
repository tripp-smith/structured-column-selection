# Application layer status

Phase 5 adds a Python CPQR selector in `structselect/cpqr.py` and a
SPEC §8 census in `structselect/census.py`. The census writes
machine-readable records (`experiments/census_seed0.json`) with
`r_CPQR`, singular values, and optional exhaustive optima. It is a
discovery witness, not a certified polynomial bound.

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
`{0,2}` with `r_CPQR = 5/8`, that leverages sum to `2`, that the
first leverage is at least `k/n`, that residuals after `{0}` sum to
`1`, that `frame23` volume is `16/25 ≥ 1/3`, that `frame12` has
volume `16/25 ≥ 1/2`, and that orthogonal-row samples return `k`
columns. The source of truth for the selected set is
`frame23_cpqr_set`; the source of truth for the card identity is
`milestoneE_cpqr_card_eq`; the source of truth for residual energy is
`milestoneE_residual_energy`; the source of truth for the binomial
volume bound is `milestoneE_cpqr_volume_ge_binomial`; the source of
truth for the `k=1` volume bound is `milestoneE_k1_volume_ge`.

When selectors are added, this document will separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.
