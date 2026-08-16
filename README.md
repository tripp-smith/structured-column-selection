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

- Milestone E structural CPQR layer (algorithm and full-rank card, not a bound)
  - `milestoneE_residual_empty`
  - `milestoneE_leverage_sum`
  - `milestoneE_first_pivot_is_max`
  - `milestoneE_first_leverage_ge`
  - `milestoneE_cpqr_card_le`
  - `milestoneE_cpqr_card_eq`
  - `milestoneE_k1_volume_ge` (`k = 1` only; workshop scale, not general `k`)
  - `milestoneE_residual_energy`
  - `milestoneE_next_residual_ge`
  - `milestoneE_cpqr_volume_ge_binomial` (exponential / not polynomial)
  - `milestoneE_mulVec_energy_le` (contraction; not an inverse bound)
  - `milestoneE_col_energy_le` (column leverage `≤ 1`; not an inverse bound)
  - `milestoneE_last_residual_ge` (last residual `≥ 1/(n-k+1)`; not a joint poly bound)
  - `milestoneE_pivot_gram_inv_trace_le` (pivot-Gram inverse trace
    `≤ (n-k+1)(4^k+6k-1)/9`; polynomial in `n`, exponential in `k`;
    not a joint `poly(n,k)` bound)
  - `milestoneE_residual_antitone` (independent residuals decrease
    when the column set grows; not an inverse-norm bound)
  - `milestoneE_residual_insert_downdate` (rank-1 residual downdate;
    not an inverse-norm bound)
  - `milestoneE_gram_inv_trace_eq_sum_inv_residual`
    (`tr(G_J⁻¹) = ∑ 1/` leave-one-out residual; not a joint poly bound)
  - `milestoneE_sigma_min_ge_inv_sqrt_trace`
    (`σ_min(A_J) ≥ 1/√tr(G⁻¹)`; not a joint poly bound)
  - `milestoneE_gsR_mul_transpose` (implicit CPQR factor `R Rᵀ = I`;
    not an inverse-norm bound)
  - `milestoneE_bidiagonal_U_inv_trace_le` (poly inverse-trace bound
    **only if** Gram–Schmidt `U` is bidiagonal; a hypothesis on `U`,
    not a class of `A`, not Path 1, not a joint `poly(n,k)` theorem)
  - `milestoneE_cpqr_inv_energy_le_choose` (`k · C(n,k)` inverse
    energy; exponential / not polynomial)
  - `milestoneE_cpqr_inv_energy_le_of_minDim` (Path 3: `k · n^d` on
    the static class `min(k, n-k) ≤ d`; not Path 1)
- Milestone E `C = 1` counterexample witness (certified, kills only
  `C = 1`): rational `3×8` `frame38` with `AAᵀ = I`, CPQR set
  `{0,1,2}`, and `r_CPQR > 1` (`frame38_mul_transpose`,
  `frame38_cpqr_set`, `frame38_inv_norm_lb` in
  `SmallInstanceChecks.lean`, plus exact Python re-certification in
  `tests/test_cpqr_r_gt_1.py`). The certified inverse norm `≈ 4.37`
  is below the campaign's named polynomial `512`, so Milestone E
  stays open. A `4×12` record with `r_CPQR ≈ 1.236`
  (`experiments/cpqr_r_gt_1_numeric_4_12.json`) is numeric only and
  not certified.
- Milestone E §8 census (witnesses only): `structselect/census.py`
- Milestone E §9 certificate automation: `structselect/certify.py`
  (Cayley / Givens; re-certifies `frame38`; does not close E)
- Milestone E Wave 1 census (witnesses only): ETF / simplex / Paley,
  clustered near-parallels, Haar `k ≤ 12` growth, block-diagonal ETF
  copies (`experiments/census_wave1_*_seed1.json`). Worst recorded
  `r_CPQR` there is `√3/2` on the Mercedes-Benz / simplex `2×3`.
- Milestone E Path 2 adverse ladder (witnesses only): trapezoidal
  search in `structselect/adverse.py`, record
  `experiments/cpqr_adverse_ladder_seed20260816.json`. Worst
  recorded instance is `(k,n)=(8,24)` with inverse norm `≈ 30.98`,
  `r_CPQR ≈ 2.66` (`≈ 0.17%` of the named polynomial). Growth looks
  polynomial through `k = 8`; no superpolynomial family.

Not yet claimed:

- a polynomial CPQR theorem for general `k`, or a counterexample past
  the named polynomial (the certified `frame38` kills only `C = 1`).
  Path 3 has a polynomial inverse-energy theorem on the static class
  `min(k, n-k) ≤ d`; that does not close Path 1.
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
- `StructuredColumnSelection/ResidualEnergy.lean`:
  Gram-projector residual energy and the next-residual average.
- `StructuredColumnSelection/CPQRVolume.lean`:
  first-pivot leverage, the `k = 1` volume bound, and the binomial
  volume lower bound (exponential, not polynomial).
- `StructuredColumnSelection/PrefixInverse.lean`:
  orthogonal-row contraction, column energy `≤ 1`, and the last
  CPQR residual average. Not a joint `poly(n,k)` inverse bound.
- `StructuredColumnSelection/TriangularBound.lean`:
  Gram–Schmidt factorization of the pivot-ordered CPQR Gram matrix,
  its Neumann-series inverse, the Businger–Golub entry bound, and
  the trace bound `tr((G')⁻¹) ≤ (n-k+1)(4^k+6k-1)/9` (polynomial in
  `n`, exponential in `k`; not a joint `poly(n,k)` bound).
- `StructuredColumnSelection/ResidualMono.lean`:
  residual monotonicity and rank-1 / CPQR residual downdate.
  Not a joint `poly(n,k)` inverse bound.
- `StructuredColumnSelection/SigmaMinBounds.lean`:
  Gram inverse-trace as a sum of reciprocal leave-one-out residuals,
  and the elementary `σ_min ≥ 1/√tr` bound. Not a joint `poly(n,k)`
  inverse bound.
- `StructuredColumnSelection/RowOrthoConstraints.lean`:
  implicit CPQR factor `R Rᵀ = I`, and a polynomial inverse-trace
  bound only under a bidiagonal hypothesis on `U` (not a class of
  `A`, not Path 1).
- `StructuredColumnSelection/StaticClass.lean`:
  binomial inverse-energy bound and the Path 3 complementary-dimension
  class `min(k, n-k) ≤ d`. Not a joint `poly(n,k)` theorem.
- `StructuredColumnSelection/SmallInstanceChecks.lean`:
  exact rational enumerations used as independent witnesses,
  including the certified `frame38` `C = 1` counterexample
  (`native_decide`, not a public structural theorem).
- `StructuredColumnSelection/Theorems.lean`:
  public theorem exports.

## Cloud Agent environment

The repository ships a minimal Cloud Agent setup in
`.cursor/environment.json` that runs `.cursor/install.sh`, which installs
Lean tooling idempotently, fetches mathlib cache, and builds the project.

## Skill cadence

Phase execution cadence is defined in:

- `.cursor/skills/autonomous-implementation/SKILL.md`
- `.cursor/skills/phase-cadence/SKILL.md`
- `.cursor/skills/e-characterization/SKILL.md`
- `.cursor/skills/verify-public-theorems/SKILL.md`
- `.cursor/rules/claim-discipline.mdc`

It covers specify → implement → verify → document → ship, with explicit
claim discipline. Verify with `bash scripts/verify.sh`.

A detailed reasoning log, failed attempts, and the next-work queue
live in `CHECKPOINT.md`. The engineering playbook is
`autonomous-implementation.md`.
