# Application layer status

Phase 5 adds a Python CPQR selector in `structselect/cpqr.py` and a
SPEC §8 census in `structselect/census.py`. The census writes
machine-readable records (`experiments/census_seed0.json`,
`experiments/census_wave1_*_seed1.json`,
`experiments/census_static_class_seed1.json`) with
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
(polynomial in `n`, exponential in `k`); residual monotonicity and
downdate are `milestoneE_residual_antitone` and
`milestoneE_residual_insert_downdate`; the Gram inverse-trace /
leave-one-out identity is
`milestoneE_gram_inv_trace_eq_sum_inv_residual`; the elementary
`σ_min ≥ 1/√tr` bound is `milestoneE_sigma_min_ge_inv_sqrt_trace`;
row-orthonormality of the implicit CPQR factor is
`milestoneE_gsR_mul_transpose`; the bidiagonal-`U` inverse-trace
bound is `milestoneE_bidiagonal_U_inv_trace_le` (hypothesis on `U`,
not a class of `A`, not Path 1); the binomial inverse-energy bound
is `milestoneE_cpqr_inv_energy_le_choose` (exponential / not
polynomial); the Path 3 complementary-dimension theorem is
`milestoneE_cpqr_inv_energy_le_of_minDim` (not Path 1).

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

`structselect/adverse.py` and
`tests/test_adverse.py` record a Path 2 trapezoidal growth search
(`experiments/cpqr_adverse_ladder_seed20260816.json`). Tests check
row-orthonormality, pivot margins, and named-poly flags; they do
not assert a universal `r_CPQR` bound. The worst recorded instance
is `(k,n)=(8,24)` with inverse norm `≈ 30.98`, `r_CPQR ≈ 2.66`
(`≈ 0.17%` of the named polynomial). Growth looks polynomial
through `k = 8`. This is a witness, not a theorem.

When selectors are added, this document will separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.

## Exact coefficient-budget checks

`structselect.column_budget.check_column_budget(rows)` accepts a rational
unit upper triangular matrix and returns Fraction column masses, budget
status, solve-column energies, maximum solve entry, and explicit finite
stop/certification labels. Invalid shape or triangular structure raises
ValueError. It solves one RHS at a time and never forms an explicit inverse.
This checks coefficients only: it neither selects pivots nor certifies that
an input arises from a row-orthogonal CPQR frame. The tests independently
use the opposite multiplication recurrence and check exact products.


## Actual volume expectation verifier (2026-10-24)

`structselect.volume_exact.exact_volume_expectation(rows, max_subsets=10000)`
accepts a nonempty exact rational orthogonal-row frame (integers, rational
strings or Fraction entries). It enumerates k-subsets and factors each Gram
with rational LDLᵀ. One RHS is solved at a time to compute the inverse trace;
an explicit inverse is never formed. Singular terms have zero weight and
`inverse_trace=None`, rather than a fabricated successful inverse.

The result contains exact Fraction expectation, normalized mass, bound and
per-subset terms. `status=exhaustive_exact` certifies the finite computation.
An insufficient subset budget returns `status=budget_exhausted`,
`certified=False`, and no partial expectation. Invalid/non-Parseval inputs,
floats and ragged/empty matrices raise ValueError. The Lean theorem includes
k=0, while this Python diagnostic intentionally requires a nonempty matrix.
This is a bounded verification tool, not the efficient reverse sampler still
required by SPEC §5. No random seed or pivot claims are involved.
