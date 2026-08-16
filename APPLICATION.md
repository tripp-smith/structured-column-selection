# Application layer status

Phase 5 adds a Python CPQR selector in `structselect/cpqr.py` and a
SPEC §8 census in `structselect/census.py`. The census writes
machine-readable records (`experiments/census_seed0.json`,
`experiments/census_wave1_*_seed1.json`) with
`r_CPQR`, singular values, pivot trajectories, and optional
exhaustive optima. It is a
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
truth for the `k=1` volume bound is `milestoneE_k1_volume_ge`;
the source of truth for contraction and the last residual is
`milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`, and
`milestoneE_last_residual_ge`; the source of truth for the
pivot-Gram inverse trace bound is `milestoneE_pivot_gram_inv_trace_le`
(polynomial in `n`, exponential in `k`).

`tests/test_cpqr_r_gt_1.py` re-certifies the `3×8` witness
`experiments/cpqr_r_gt_1_witness_3_8.json` in exact `Fraction`
arithmetic: `AAᵀ = I`, CPQR selects `{0,1,2}` with strictly positive
pivot margins, and `18‖A_J x‖² < ‖x‖²`, i.e. `r_CPQR > 1`. The Lean
source of truth is `frame38_mul_transpose`, `frame38_cpqr_set`, and
`frame38_inv_norm_lb` in `SmallInstanceChecks.lean` (`native_decide`;
not exported as a public structural theorem). The witness refutes
only the ideal `C = 1` bound: the certified inverse norm stays below
the named polynomial `512`, so Milestone E remains open. The `4×12`
record `experiments/cpqr_r_gt_1_numeric_4_12.json`
(`r_CPQR ≈ 1.236`) is a float observation and is not certified.

`structselect/certify.py` automates the SPEC §9 pipeline: Cayley
transform of a rational skew-symmetric matrix (coefficient
denominator `D`) and/or rational Givens rotations from Pythagorean
triples, then exact `AAᵀ = I`, unique CPQR pivot margins, and an
explicit rational test vector for `c · ‖A_J x‖² < ‖x‖²`. Tests in
`tests/test_certify.py` re-certify `frame38` both from the published
rationals and after Cayley re-parametrization of the float matrix.
The automation does not close Milestone E: `C = 1` witnesses stay
below the named polynomial, and Cayley rounding of the `4×12` float
record does not preserve `r_CPQR > 1`.

When selectors are added, this document will separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.
