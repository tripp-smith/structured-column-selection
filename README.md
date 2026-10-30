# structured-column-selection

Lean 4 formalization and computational study of quasi-optimal RRQR/CSSP
under orthogonal-row structure (`A Aᵀ = I`) for Simons Workshop Problem 4.1.

## Status

Machine-checked randomized quasi-optimal column selection for the
orthogonal-row case of Simons Problem 4.1.

The current reverse-sampling phase supplies an exact rational executable
sampler alongside the all-real finite kernel theorem. Python/RNG extraction
into Lean is not claimed. Unconditional inverse-expectation equality is false with
singular support; the audited inequality and probability theorem are listed
below. CPQR outcome 2 is the explicit adverse family below. A polynomial
bound for every orthogonal-row matrix is not claimed. The CSSP comparison is
`milestoneF_cssp_spectral` and `milestoneF_cssp_frobenius`: for a supplied
factor `A = U S Qᵀ + E` with `Qᵀ Q = 1` and invertible `Q_J`,
`‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖` in spectral norm and in Frobenius norm,
where `T = (Q_Jᵀ)⁻¹ Qᵀ`.

Phases completed:

- Milestone A (structural foundations)
  - `milestoneA_transpose_correspondence`
  - `milestoneA_selectedSquare_entry`
  - `milestoneA_selectedGram_formula`
- Milestone B (volume normalisation)
  - `milestoneB_cauchyBinet`
  - `milestoneB_volume_normalization`
- Milestone C (exact adjugate identity; actual inverse equality needs full support)
  - `milestoneC_adjugate_sum`
  - `milestoneC_inverse_gram_expectation`
- Milestone D (finite adjugate proxy expectation and Markov tail; actual bridge below)
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

The original-SPEC obligation ledger is the table at the top of `RESEARCH.md`.
Proved Milestone E lemmas stay in the module map below and do not close that
table's three E outcomes. Frozen census files are indexed by
`experiments/manifest.json`.

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
- `StructuredColumnSelection/MathlibReady.lean`:
  expected-type checks for the Cauchy–Binet, volume, and finite Markov
  candidates. Not a mathlib pull request.

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

Completed bounded phase: **E column budget — verified**. Delivered Lean outputs: `milestoneE_column_budget_S_abs_le_one` and
`milestoneE_column_budget_inv_trace_le`, with inverse trace bounded by
`k(k+1)(n-k+1)/2` under `gsUColumnBudget`. Root `./scripts/verify.sh` passes: Lean build, no proof placeholders or
custom axioms, default-axiom audit for all 34 public theorems, and 70 Python
tests. CI passes; current revision checks are linked from the draft PR. This allows
coupling beyond bidiagonal support. General Milestone E remains open.

Draft PR: [#13](https://github.com/tripp-smith/structured-column-selection/pull/13).
Branch: `codex/phase-e-column-budget`. Skills and workflow provenance are in
`.agents/WORKFLOW_IMPORT.md`.

Completed phase: **D actual inverse — implemented; verification/delivery receipt
on the phase PR**. Estimated original-objective completion after this phase:
**50%**, with uncertain research effort. Public outputs:
`milestoneD_actual_expected_inv_trace_le`,
`milestoneD_actual_expected_inv_trace_eq_of_full_support`,
`milestoneD_singular_volume_mass_zero`,
`milestoneD_actual_inv_trace_good_mass`,
`milestoneD_actual_inverse_energy_good_mass`, and
`milestoneD_actual_expectation_equality_obstruction`.
The last result certifies why the original unconditional equality cannot be
claimed. An exact enumeration verifier is included; the efficient sampler
remains the next executable obligation. See RESEARCH.md and the phase PR for
original obligations, exact-revision checks, and delivery status.

Phase PR and canonical verification/delivery receipt:
[#14](https://github.com/tripp-smith/structured-column-selection/pull/14).

Completed phase: **D reverse volume sampling — verified and merged (PR #15)**.
The public `volume_sample` API and `python3 -m structselect` run a bounded exact
hybrid reverse sampler with rational LDLᵀ and solve-based certificates. The
finite kernel law is `milestoneD_reverse_sampler_law`; its actual inverse-energy
guarantee is `milestoneD_reverse_inverse_energy_good_mass`. Public deletion,
Gram-determinant and score-ratio theorems connect the model to matrix quantities.
`milestoneD_reverse_fast_proposal_sum_le` is an explicit finite proposal-mean
sum bound, not a machine runtime theorem. Tests use exact full-state propagation,
independent determinants and LDLᵀ reconstruction, including failure paths.

Estimated completion after the CSSP delivery: **about 80%** of original
obligations, with uncertain research effort. The sampler gap is addressed.
Outcome 2 of Milestone E is closed by the family and polynomial quantifiers
below. Milestone F is closed by `milestoneF_cssp_spectral` and
`milestoneF_cssp_frobenius`. Outcome 1, outcome 3, remaining comparison APIs
and the final full-contract audit remain open. The original unconditional
inverse expectation equality remains refuted.

Reverse-sampling phase and canonical verification/delivery receipt:
[#15](https://github.com/tripp-smith/structured-column-selection/pull/15).

Completed bounded phase: **E wide completion and prefix core — verified (PR #16)**;
verification and delivery status are in the phase PR receipt. Public outputs:
`milestoneE_wide_completion_orthogonal`,
`milestoneE_triangular_prefix_projector`,
`milestoneE_triangular_prefix_residual`,
`milestoneE_triangular_prefix_pivots`, and
`milestoneE_wide_parameter_diagonal_lower`.
These prove finite completion, coordinate residual identities, and an actual
CPQR sequence under explicit strict tail-energy hypotheses. Exact compressed
checks use independent bordered-Gram determinants and witness multiplication.
The all-parameter adverse family is the next phase. Randomized volume
sampling is separate.

Phase PR and canonical verification/delivery receipt:
[#16](https://github.com/tripp-smith/structured-column-selection/pull/16).

Completed phase: **E explicit adverse family — outcome 2**. Outcome 2 is
`milestoneE_wide_adverse_family` (every `m ≥ 2`: orthogonal rows, CPQR set
equal to the leading `m²` columns, image energy `1`, inverse energy at least
`((2m/3)(4/3)^(m-1))²`), consumed by
`milestoneE_cpqr_no_joint_polynomial` (every degree `d` and every `C > 0`:
`C(n+k+1)^{2d} ‖A_J x‖² < ‖x‖²`) and
`milestoneE_cpqr_named_polynomial_obstruction`
(`max(n³, k³, (k(n-k+1))²)² ‖A_J x‖² < ‖x‖²`). This is not a polynomial
bound for every orthogonal-row matrix. Outcomes 1 and 3 remain open. The
contract and delivery note are in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#18](https://github.com/tripp-smith/structured-column-selection/pull/18).

Completed phase: **F CSSP bridge**. `milestoneF_cssp_spectral` and
`milestoneF_cssp_frobenius` prove
`‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖` for `A = U S Qᵀ + E`, `Qᵀ Q = 1`,
invertible `Q_J`, and `T = (Q_Jᵀ)⁻¹ Qᵀ`. The first norm is spectral and the
second is Frobenius; the coefficient is spectral in both. The factor is
supplied. This is not a polynomial CPQR bound, and it does not solve
Problem 4.1. Outcomes 1 and 3 stay open. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#19](https://github.com/tripp-smith/structured-column-selection/pull/19).

Completed phase: **G wide leverage escape**. `milestoneE_wide_leverage_escape`
shows that for every `τ ≥ 0` some outcome-2 frame has two column energies
with ratio greater than `τ` and greater than `8 m²`. Every fixed leverage
ratio therefore excludes a large member of that family. This is not a
polynomial bound on the leverage-ratio class, and it does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#20](https://github.com/tripp-smith/structured-column-selection/pull/20).

Completed phase: **H inverse-trace step**. `milestoneE_append_inv_trace_increment`
says that appending a column increases the Gram inverse trace by
`(1 + ‖G⁻¹ Bᵀ v‖²) / residual`. This is not the standard CPQR pivot, not a
polynomial inverse bound, and it does not close outcome 3. The contract is
in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#21](https://github.com/tripp-smith/structured-column-selection/pull/21).

Completed phase: **I best-column increment**.
`milestoneE_best_column_increment_le` says that for an invertible selected
Gram with fewer than `k` columns, some unused column has positive residual
and inverse-trace increment at most
`((n - t) + trace(G⁻¹) - t) / (k - t)`. This is not a CPQR bound and it
does not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#22](https://github.com/tripp-smith/structured-column-selection/pull/22).

Completed phase: **J inverse-trace growth step**.
`milestoneE_inv_trace_growth_step` says that if the selected inverse
trace is at most `t (n - t + 1) / (k - t + 1)`, some appended column
brings it to at most `(t + 1) (n - t) / (k - t)`. This is not a CPQR
bound and it does not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#23](https://github.com/tripp-smith/structured-column-selection/pull/23).

Completed phase: **K inverse-trace induction**.
`milestoneE_minimizing_inv_trace_le` says some `k` columns chosen by the
increment bound have invertible Gram and inverse trace at most
`k (n - k + 1)`. This is not a CPQR bound and it does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#24](https://github.com/tripp-smith/structured-column-selection/pull/24).

Completed phase: **L inverse spectral bound**.
`milestoneE_minimizing_inv_spectral_le` says the increment pivot selects
`k` columns satisfying `‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. This is not a
CPQR bound and it does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#25](https://github.com/tripp-smith/structured-column-selection/pull/25).

Completed phase: **M increment set**.
`milestoneE_increment_set_bound` says the least-index minimizer of the
inverse-trace increment selects `k` columns with inverse trace at most
`k (n - k + 1)` and squared inverse operator norm at most
`1 + k (n - k)`. This is not a CPQR bound and it does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#26](https://github.com/tripp-smith/structured-column-selection/pull/26).

Completed phase: **N pivot split**.
`milestoneE_increment_set_ne_cpqr` says there is an orthogonal-row
`2×5` matrix on which max-residual CPQR selects `{0, 1}` and the
least-index increment pivot selects `{0, 2}`. This does not close
outcome 1 or outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#27](https://github.com/tripp-smith/structured-column-selection/pull/27).

Completed phase: **O zero-coefficient pivot**.
`milestoneE_zero_coeff_same_pivot` says that a zero coefficient on every
positive-residual unused column makes the increment pivot and
max-residual CPQR return the same column. This does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#28](https://github.com/tripp-smith/structured-column-selection/pull/28).

Completed phase: **P orthogonal-column CPQR**.
`milestoneE_incoherent_zero_cpqr_bound` says pairwise orthogonal columns
make max-residual CPQR select `k` columns with inverse trace at most
`k (n - k + 1)` and squared inverse operator norm at most
`1 + k (n - k)`. This class is stricter than the SPEC §10 target and
does not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#29](https://github.com/tripp-smith/structured-column-selection/pull/29).

Completed phase: **Q adverse family outside orthogonal columns**.
`milestoneE_wide_not_incoherent_zero` says that for every `m ≥ 2` the
outcome-2 frame has a nonzero column inner product, so the phase-P
bound does not apply to it. This does not close outcome 3. The contract
is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#30](https://github.com/tripp-smith/structured-column-selection/pull/30).

Completed phase: **R equal-energy second pivot**.
`milestoneE_equal_energy_cpqr_prefix_trace` says equal column energy
makes the first CPQR pivot column `0`, makes the second CPQR pivot agree
with the increment pivot, and bounds the two-column inverse trace by
`2 (n - 1) / (k - 1)`. This does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#31](https://github.com/tripp-smith/structured-column-selection/pull/31).

Completed phase: **S equal-energy prefix Rayleigh**.
`milestoneE_equal_energy_cpqr_prefix_rayleigh` says equal column energy
makes the two-column CPQR Rayleigh quotient at least
`(k - 1) / (2 (n - 1))`. This bounds only that prefix and does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#32](https://github.com/tripp-smith/structured-column-selection/pull/32).

Completed phase: **T equal-energy three-column trace**.
`milestoneE_equal_energy_cpqr_three_trace` says equal column energy
makes the CPQR three-column inverse trace at most the two-column bound
plus one Rayleigh-controlled step. This bounds only that prefix and does
not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#33](https://github.com/tripp-smith/structured-column-selection/pull/33).

Completed phase: **U equal-energy three-row CPQR**.
`milestoneE_equal_energy_cpqr_k3` says that when `k = 3`, equal column
energy makes the full CPQR set obey `5n - 12 + 6/n` in inverse trace and
in inverse energy. This is not a bound for general `k` and does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#34](https://github.com/tripp-smith/structured-column-selection/pull/34).

Completed phase: **V leverage-ratio pivot split**.
`milestoneE_leverage_ratio_pivot_split` gives an orthogonal-row `2×5`
frame with column energies in `[13/50, 16/25]`, leverage ratio `32/13`,
on which max-residual CPQR and the increment pivot select different
columns. Equal energy still makes the second pivots agree. This does not
close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#35](https://github.com/tripp-smith/structured-column-selection/pull/35).

Completed phase: **W orthogonal equal-energy block**.
`milestoneE_equal_energy_orthogonal_block_same_pivot` says that equal
column energy and a pairwise-orthogonal selected block make the next
CPQR pivot agree with the increment pivot. A one-column block is the
agreement half of the equal-energy second pivot. This does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#36](https://github.com/tripp-smith/structured-column-selection/pull/36).

Completed phase: **X equal-energy block split**.
`milestoneE_equal_energy_block_pivot_split` gives an orthogonal-row
`3×6` frame with equal column energy `1/2` on which columns `0` and `1`
have inner product `31/100`. After that block, max-residual CPQR takes
column `5` and the increment pivot takes column `3`. Column `5` is
orthogonal to column `0`. This does not say the CPQR set differs from
the increment set, and it does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#37](https://github.com/tripp-smith/structured-column-selection/pull/37).

Completed phase: **Y equal-energy third pivot**.
`milestoneE_equal_energy_third_pivot_split` gives an orthogonal-row
`3×6` frame with equal column energy `1/2`. Both rules take column `0`
and then column `2`. After `{0, 2}`, max-residual CPQR takes column `3`
and the increment pivot takes column `5`, so the three-column sets
differ. Columns `0` and `2` are not orthogonal. This does not close
outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#38](https://github.com/tripp-smith/structured-column-selection/pull/38).

Completed phase: **Z absolute incoherence escape**.
`milestoneE_incoherent_no_joint_polynomial` says that for every `ρ > 0`,
some orthogonal-row frame in `ColumnIncoherent A ρ` has a CPQR block whose
inverse energy exceeds `C (n + k + 1)^{2d}`. The predicate bounds absolute
inner products. The normalized coherence ratio is a different condition,
and `ρ = 0` is unchanged. This does not close outcome 3. The contract is
in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#39](https://github.com/tripp-smith/structured-column-selection/pull/39).

Completed phase: **AA normalized coherence**.
`milestoneE_normalized_coherence_one` says that the outcome-2 frame has
two equal positive columns, so their normalized coherence is `1`, and
that frame still beats `C (n + k + 1)^{2d}`. A class that requires every
normalized ratio to be at most some `ρ < 1` excludes this frame. The
theorem does not give a polynomial CPQR bound on a stricter ratio.
Absolute inner-product incoherence is a different predicate. This does
not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#40](https://github.com/tripp-smith/structured-column-selection/pull/40).

Completed phase: **AB design-padded adverse family**.
`milestoneE_design_adverse_family` replaces the repeated filler block of
the outcome-2 frame by an arbitrary tight design `W` with `W Wᵀ = 1` and
column energy at most `1 / wideRepeats m`. For every completion `C` of
the triangular block, `[R | C W]` has orthogonal rows, CPQR takes the
leading prefix, the image energy is `1`, and the inverse energy is at
least `wideGrowthLower m ^ 2`. No coherence bound on the resulting
columns is claimed. This does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#41](https://github.com/tripp-smith/structured-column-selection/pull/41).

Completed phase: **AC symmetric completion**.
`milestoneE_symmetric_completion` gives, for every `R` with
`‖R‖_F² ≤ 1`, a symmetric completion `R Rᵀ + C Cᵀ = 1` with
`⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`,
`(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and
`‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`. The perturbation bound uses
`(C + I)(C - I) = -R Rᵀ` and `C ⪰ 0`. No coherence bound on any frame
is claimed. This does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#42](https://github.com/tripp-smith/structured-column-selection/pull/42).

Completed phase: **AD weighted signed triple design**.
`milestoneE_triple_design` gives, for every `n`, an explicit tight
design `W Wᵀ = 1` in `ℝ^(n+3)` with `4 (n+3)(n+2)(n+1)` columns, equal
column energy `1 / (4 (n+2)(n+1))`, and pairwise normalized inner
product at most `13/14` (attained). Columns are
`e_p + 2σ e_{q'} + 3τ e_{r'}` over distinct coordinates, normalized by
`√(56 (n+2)(n+1))`. The column energy is above the `1 / wideRepeats`
cap of `milestoneE_design_adverse_family`, so no adverse frame and no
coherence bound on any orthogonal-row frame is claimed. This does not
close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#43](https://github.com/tripp-smith/structured-column-selection/pull/43).

Completed phase: **AE scaled leading block**.
`milestoneE_scaled_triple_frame` gives, for every `m ≥ 3`, the
orthogonal-row frame `[3 R₀ | C W]` with `R₀ = wideTriangular m`, the
symmetric completion `C` of `3 R₀`, and the triple design `W`: CPQR set
equal to the leading prefix, image energy `1`, and inverse energy at
least `((2m/3)(4/3)^(m-1))² / 9`. The inputs are the row-structure bound
`‖R₀‖_F² ≤ 5 / (16 k)` and the contraction `‖C w‖² ≤ ‖w‖²`, which put
the design energy `1 / (4 (k-1)(k-2))` under the scaled threshold
`9 / (16 k²)` for `k ≥ 5`. The statement records the completion
identities of `C` and the design properties of `W`. No coherence bound
on the columns of the frame is claimed. This does not close outcome 3.
The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#44](https://github.com/tripp-smith/structured-column-selection/pull/44).

Completed phase: **AF frame coherence, filler pairs**.
`milestoneE_scaled_triple_frame_filler_coherence` gives, for every
`m ≥ 3`, the scaled triple-design frame of phase AE together with two
normalized-coherence bounds: distinct filler columns at most
`(13/14 + ε)/(1 - ε)`, and each leading column against each filler at
most `(3(1 + 1/m)/√14 + ε)/√(1 - ε)`, where `ε = 45/(16 k)`.
This phase does not bound leading–leading pairs, and no coherence bound
on the whole frame is claimed. This does not close outcome 3. The contract
is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#45](https://github.com/tripp-smith/structured-column-selection/pull/45).

Completed phase: **AG leading–leading coherence**.
`milestoneE_scaled_block_leading_coherence` gives, for every `m ≥ 2` and
all distinct columns of `scaledBlock m = (3 : ℝ) • wideTriangular m`,
normalized coherence at most `1/2 + 1/m`. The constant was not weakened.
This does not bound filler pairs, and a leading–leading ratio
`≤ 1/2 + 1/m` is not a coherence bound on the whole frame. This does not
close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#46](https://github.com/tripp-smith/structured-column-selection/pull/46).

Completed phase: **AH bounded coherence is not polynomial**.
`milestoneE_bounded_coherence_no_polynomial` shows that normalized
coherence at most `19/20` does not restore a polynomial CPQR bound.
For every degree `d` and every `C > 0`, the scaled triple-design frame
at a large `m` has orthogonal rows, positive column energy, normalized
coherence at most `19/20`, and CPQR inverse energy strictly above
`C (n+k+1)^{2d}`. Any cap `ρ ≥ 19/20` is too weak for the same reason:
coherence at most `19/20` implies coherence at most `ρ`. A stricter cap
is not ruled out. The constant `19/20` was not weakened. This does not
close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#47](https://github.com/tripp-smith/structured-column-selection/pull/47).

Completed phase: **AI joint leverage-coherence census**.
`experiments/census_joint_seed1.json` is a float census, seed 1, of
orthogonal-row frames with leverage ratio at most `8` and normalized
coherence at most `0.9`, for `k = 2..8` and `n ≤ 16`. The largest
recorded `r_CPQR` is `0.866025403784439`, on the `2×3` simplex ETF.
Every cell of `τ ∈ {2, 4, 8}` and `ρ ∈ {0.5, 0.7, 0.9}` was populated.
Inside each populated cell the per-`k` maximum did not increase with
`k`. No accepted frame had `r_CPQR > 1`. The sample does not prove the
joint class is safe and does not prove it grows. The scaled
triple-design frame is leverage-unbalanced and is not in the sample.
The coherence cap `19/20` does not exclude this class, because that
family has wildly unbalanced leverages. This does not close outcome 3.
The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#48](https://github.com/tripp-smith/structured-column-selection/pull/48).

Completed phase: **AJ joint pair Gram**.
`milestoneE_joint_pair_inv_trace` bounds every 2-column Gram under a
leverage ratio at most `τ` and normalized coherence at most `ρ < 1`.
For orthogonal rows with `2 ≤ k` and `1 ≤ n`, the Gram
`selectedColGram A {i, j}` is invertible and its inverse trace is at
most `2 τ^2 n / (k (1 - ρ^2))`. The constant was not weakened. This is
not a bound on a `k`-set for `k > 2`, and it does not identify
`cpqrIterate A 2`. This does not close outcome 3. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#49](https://github.com/tripp-smith/structured-column-selection/pull/49).

Completed phase: **AK joint CPQR prefix**.
`milestoneE_joint_cpqr_prefix_trace` specializes the two-column inverse-trace
bound to the CPQR prefix of length 2. Under the same leverage-ratio and
coherence hypotheses, plus `2 ≤ n`, there are distinct columns `j0` and
`j1` with `cpqrIterate A 2 = {j0, j1}`, the Gram
`selectedColGram A (cpqrIterate A 2)` invertible, and its inverse trace at
most `2 τ^2 n / (k (1 - ρ^2))`. The constant was not weakened. This does
not bound later pivots. A 2-column CPQR prefix is not a `k`-set for
`k > 2`. This does not close outcome 3. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#50](https://github.com/tripp-smith/structured-column-selection/pull/50).

Completed phase: **AL joint CPQR Rayleigh**.
`milestoneE_joint_cpqr_prefix_rayleigh` is the Rayleigh form of the length-2
CPQR prefix under the joint leverage-ratio and coherence hypothesis. For
every `x` on `cpqrIterate A 2`,
`k (1 - ρ^2) / (2 τ^2 n) · ‖x‖² ≤ ‖selectedCols A (cpqrIterate A 2) x‖²`.
The coefficient is the reciprocal of the phase-AK inverse-trace bound and
was not weakened. On the `2×2` identity the coefficient is `1/2` while the
Rayleigh quotient is `1`, because `λ_max ≤ trace`. The bound is not sharp.
It does not bound later pivots. It does not close outcome 3. It is not a
polynomial bound for every orthogonal-row matrix. The contract is in
RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#51](https://github.com/tripp-smith/structured-column-selection/pull/51).

Completed phase: **AM joint third CPQR pivot**.
`milestoneE_joint_cpqr_three_trace` bounds the inverse trace of
`selectedColGram A (cpqrIterate A 3)` under the joint leverage-ratio and
coherence hypothesis, plus `3 ≤ k`. The bound is
`2 τ^2 n / (k (1 - ρ^2)) + (1 + 2 τ^3 / (1 - ρ^2)) · (n - 2) / (k - 2)`.
The constant was not weakened. On the `3×3` identity the inverse trace
is `3` and the formula at `τ = 1`, `ρ = 0`, `k = 3`, `n = 3` equals `5`.
The bound is not sharp. This does not bound pivots after the third.
A 3-column prefix is not a bound for general `k`. This does not close
outcome 3. It is not a polynomial bound for every orthogonal-row matrix.
The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#52](https://github.com/tripp-smith/structured-column-selection/pull/52).

Completed phase: **AN joint three-row CPQR**.
`milestoneE_joint_cpqr_k3` says that when `k = 3`, the joint
leverage-ratio and coherence hypothesis bounds the full CPQR set, not
only a length-3 prefix. The set has three columns,
`selectedColGram A (cpqrSet A)` is invertible, its inverse trace is at
most `2 τ^2 n / (3 (1 - ρ^2)) + (1 + 2 τ^3 / (1 - ρ^2)) · (n - 2)`, and
`‖x‖² ≤ B ‖selectedCols A (cpqrSet A) x‖²` for that same `B`. The
constant was not weakened. On the `3×3` identity the inverse trace is
`3` and `B` at `τ = 1`, `ρ = 0`, `n = 3` equals `5`. The bound is not
sharp. This is not a bound for general `k`. Fixing `k = 3` does not
close outcome 3. It is not a polynomial bound for every orthogonal-row
matrix. The contract is in RESEARCH.md.

Phase PR and canonical verification/delivery receipt:
[#53](https://github.com/tripp-smith/structured-column-selection/pull/53).

Completed phase: **AO CPQR trace step**.
`milestoneE_joint_cpqr_step` is one CPQR pivot step under a leverage-ratio
bound, assuming a trace bound on the current prefix. If the inverse trace
of `selectedColGram A (cpqrIterate A t)` is at most `B`, then
`selectedColGram A (cpqrIterate A (t + 1))` is invertible and its inverse
trace is at most
`B + (1 + (τ k / n) B) · (n - t) / (k - t)`.
The constant was not weakened. On the `3×3` identity the length-2 Gram is
`I₂` with inverse trace `2`. At `B = 2`, `τ = 1`, `k = 3`, `n = 3`,
`t = 2` the step bound equals `5`, and the length-3 inverse trace is `3`,
so `3 ≤ 5`. The check does not assert equality. This is one step from
length `t` to length `t + 1`. The recurrence is not iterated here. This
is not a bound on the full `k`-set. It is not a polynomial bound. It does
not close outcome 3. Coherence is not used. The contract is in RESEARCH.md.
