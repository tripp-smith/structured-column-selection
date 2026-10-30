# Research threads

## Original-SPEC obligation ledger

This is the canonical reading of SPEC §16 and §19. A later phase note does
not close an open row. Historical thread entries below are delivery logs.

| Obligation | State | What counts | What does not count |
| --- | --- | --- | --- |
| A. Transpose correspondence and selected-column algebra | closed | `milestoneA_*` | |
| B. Volume weights sum to 1 | closed | `milestoneB_cauchyBinet`, `milestoneB_volume_normalization` | |
| C. Finite inverse-Gram identity | closed as the adjugate sum | `milestoneC_adjugate_sum`, `milestoneC_inverse_gram_expectation` | a naive inverse that drops singular blocks |
| D. All-frame actual inverse expectation | the unconditional equality is false | `milestoneD_actual_expectation_equality_obstruction`, the inequality `milestoneD_actual_expected_inv_trace_le`, and `milestoneD_actual_inverse_energy_good_mass` | the original boxed equality |
| D. Efficient reverse sampler | closed as a finite kernel law | `milestoneD_reverse_sampler_law` | a claim that Python draws are formally extracted |
| E outcome 1. Polynomial CPQR bound for every orthogonal-row matrix | open | a `Theorems.lean` statement whose hypotheses are only row orthogonality and whose bound is polynomial in `n` and `k` | `4^k` trace, binomial `C(n,k)`, `k = 1`, `k = 2`, bidiagonal `U`, column budget, or `MinDimLe` |
| E outcome 2. Machine-checked counterexample past the named polynomial | closed | `milestoneE_wide_adverse_family`, `milestoneE_cpqr_no_joint_polynomial`, and `milestoneE_cpqr_named_polynomial_obstruction`: for every `m ≥ 2`, exact `AAᵀ = I`, CPQR set equal to the leading prefix, image energy `1`, and `‖x‖² ≥ ((2m/3)(4/3)^(m-1))²`; for every `d` and `C > 0`, `C(n+k+1)^{2d} ‖A_J x‖² < ‖x‖²`; and the `d = 4`, `C = 1` case `max(n³, k³, (k(n-k+1))²)² ‖A_J x‖² < ‖x‖²` | `frame38` (kills only `C = 1`; about `4.37` against `512`), the float `4×12` record, and scalar crossings with `frame_certified = False` |
| E outcome 3. That counterexample plus a weaker static class with a polynomial theorem | open | outcome 2 together with a class read from `A` alone | Path 3 `milestoneE_cpqr_inv_energy_le_of_minDim`, which has no named-polynomial counterexample beside it |
| F. CSSP perturbation bridge | closed | `milestoneF_cssp_spectral` and `milestoneF_cssp_frobenius`: for `A = U S Qᵀ + E` with `Qᵀ Q = 1` and invertible `Q_J`, `‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖` in spectral norm and in Frobenius norm, with `T = (Q_Jᵀ)⁻¹ Qᵀ` and the same spectral coefficient on the right | a truncated-SVD construction, or starting F before an E row closes |

Census files are listed in `experiments/manifest.json`. They are numeric
unless that manifest says the `3×8` witness, and that witness is still a
computational certificate in `SmallInstanceChecks.lean`. Expected-type
consumers for the weaker E hypotheses live in `scripts/CompletionContract.lean`.

Current audit (2026-10-29): historical C/D completion entries below refer to
adjugate cores. The original all-frame actual-inverse equality is false.
Outcome 2 of Milestone E is the adverse-family delivery. Milestone F is
the CSSP delivery at the end of this file. Outcomes 1 and 3 remain open.

## Thread 1 — Milestone A (completed)

Delivery:

- `milestoneA_transpose_correspondence`
- `milestoneA_selectedSquare_entry`
- `milestoneA_selectedGram_formula`

These establish the first formal contract from `SPEC.md`:
orthogonal-row/orthogonal-column transpose correspondence plus basic
selected-column algebra needed for subsequent determinant and expectation
identities.

## Thread 2 — Milestone B (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneB_cauchyBinet` | `det(AB) = ∑_{#S=k} det(A_S) det(B^S)` | `CauchyBinet.lean` | `frame23` / `frame12` enumerations |
| `milestoneB_volume_normalization` | `AAᵀ = I ⇒ ∑_{#J=k} det(A_J)² = 1` | `VolumeWeights.lean` | same, plus Python `tests/test_volume_normalization.py` |

## Thread 3 — Milestone C (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneC_adjugate_sum` | `∑_{#J=k} adj(A_J A_Jᵀ) = (n+1-k) adj(AAᵀ)` | `InverseGramExpectation.lean` | `frame23_inverse_gram_sum` |
| `milestoneC_inverse_gram_expectation` | `AAᵀ = I ⇒ ∑ adj(A_J A_Jᵀ) = (n+1-k) I` | `InverseGramExpectation.lean` | same, plus `tests/test_inverse_gram.py` |

The boxed SPEC formula is formalized with adjugates. That matches
`det² • inverse` on invertible column sets and keeps the singular
summands.

Non-claims (intentional):

- no high-probability RRQR bound in Phase 3
- no CPQR statement
- no claim that Problem 4.1 is solved
- Python is a witness, not a source of truth

## Thread 4 — Milestone D (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneD_expected_inv_frob_sq` | `AAᵀ = I ⇒ ∑ tr(adj(A_J A_Jᵀ)) = k(n-k+1)` | `InverseNormBounds.lean` | `frame23_expected_inv_frob` |
| `milestoneD_markov_inv_frob` | volume mass of `{δ tr(adj) > k(n-k+1) w}` is `≤ δ` | `InverseNormBounds.lean` | same, plus `tests/test_inverse_norm.py` |

The expectation is the trace of the Milestone C identity. The tail is a
finite Markov inequality on those traces; it is the Theorem R1
high-probability bound with `‖·‖_F` in place of `‖·‖_2` (which is
stronger on the invertible locus).

Non-claims (intentional):

- no measure-theoretic probability space
- no CPQR statement
- no CSSP bridge
- no claim that Problem 4.1 is solved
- Python is a witness, not a source of truth

## Thread 5 — Milestone E structural CPQR (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_residual_empty` | empty residual is column energy `∑_i A_{ij}²` | `ColumnPivotedQR.lean` | `tests/test_cpqr.py` leverages |
| `milestoneE_cpqr_card_le` | `#(cpqrSet A) ≤ k` | `ColumnPivotedQR.lean` | frame23 / frame12 cardinalities |
| `milestoneE_leverage_sum` | `AAᵀ = I ⇒ ∑_j residualSq A ∅ j = k` | `ColumnPivotedQR.lean` | frame23 energies `1 + 9/25 + 16/25 = 2` |
| `milestoneE_first_pivot_is_max` | a first pivot maximises empty residual | `ColumnPivotedQR.lean` | frame23 first pivot is column `0` |
| `milestoneE_first_leverage_ge` | a first pivot has leverage `≥ k/n` | `CPQRVolume.lean` | frame23 first leverage `1 ≥ 2/3` |
| `milestoneE_cpqr_card_eq` | `AAᵀ = I ⇒ #(cpqrSet A) = k` | `ColumnPivotedQR.lean` | frame23 / frame12 cardinalities |
| `milestoneE_k1_volume_ge` | `k=1 ⇒ volumeWeight(cpqrSet) ≥ n⁻¹` | `CPQRVolume.lean` | `frame12` volume `16/25 ≥ 1/2` |
| `milestoneE_residual_energy` | `AAᵀ = I`, Gram invertible `⇒ ∑ residualSq = k-#J` | `ResidualEnergy.lean` | frame23 after `{0}`: `0+9/25+16/25=1` |
| `milestoneE_next_residual_ge` | unused max residual `≥ (k-#J)/(n-#J)` | `ResidualEnergy.lean` | frame23 after `{0}`: `16/25 ≥ 1/2` |
| `milestoneE_cpqr_volume_ge_binomial` | `volumeWeight(cpqrSet) ≥ 1/C(n,k)` (not polynomial) | `CPQRVolume.lean` | frame23 `16/25 ≥ 1/3`; frame12 `16/25 ≥ 1/2` |
| `milestoneE_mulVec_energy_le` | `AAᵀ = I ⇒` energy of `A x` is `≤` energy of `x` | `PrefixInverse.lean` | column energies `≤ 1` |
| `milestoneE_col_energy_le` | `AAᵀ = I ⇒` column leverage `≤ 1` | `PrefixInverse.lean` | frame23 leverages `1, 9/25, 16/25` |
| `milestoneE_last_residual_ge` | last CPQR residual `≥ 1/(n-k+1)` | `PrefixInverse.lean` | frame23 last residual `16/25 ≥ 1/2` |
| `milestoneE_pivot_gram_inv_trace_le` | `tr((G')⁻¹) ≤ (n-k+1)(4^k+6k-1)/9` (poly in `n`, exp in `k`) | `TriangularBound.lean` | `frame23` pivot Gram trace |

Independent computational witness: `frame23_cpqr_set` selects `{0,2}` with `r_CPQR = 5/8`.

The card identity is a full-rank stopping theorem: CPQR on an
orthogonal-row matrix cannot halt before `k` columns. The `k = 1`
volume bound is a workshop-scale inverse-magnitude theorem for a
single orthonormal row. Residual energy and the binomial volume bound
are identities for every orthogonal-row matrix; `1/C(n,k)` is
exponential in `k` when `n ≈ 2k` and is not a `poly(n,k)` inverse-norm
bound. None of these closes Milestone E.

## Thread 5b — Milestone E characterization census (in progress)

SPEC §8 census contract (not a characterization outcome):

| Artifact | Statement | File | Independent check |
| --- | --- | --- | --- |
| `run_census` | Haar, Hadamard, Fourier, leverage-skew, near-duplicate, Kahan-like frames | `structselect/census.py` | `tests/test_census.py` |
| `experiments/census_seed0.json` | recorded `r_CPQR`, `σ_min`, pivots, optional exhaustive opt | `experiments/` | regenerate with seed 0 |

On the seed-0 sweep the worst recorded ratio is Hadamard `k=3,n=8`
with `r_CPQR = 2/3 < 1`. Several Haar draws are slightly worse than
the exhaustive optimum and still below the workshop scale.

Wave 1 (seed 1): Mercedes-Benz / simplex / Paley / icosahedral ETFs,
clustered near-parallels, Haar `k ≤ 12`, and block-diagonal ETF
copies. Worst recorded `r_CPQR` is `√3/2` on the `2×3` simplex /
Mercedes-Benz frame. No sample exceeded `r = 1` or the named
polynomial yardstick. The simplex saturates `1/C(n,k)` and
`σ_min = |det|` at `n = k+1`; clustered near-parallels do not
survive `row_orthonormalize`. JSON:
`experiments/census_wave1_*_seed1.json`.

This is **not** a polynomial CPQR theorem and **not** a
machine-checked counterexample. Milestone E remains open.

## Thread 5c — Milestone E triangular bound and `C = 1` witness (Wave 4)

Formal (proved, default axioms only):

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_pivot_gram_inv_trace_le` | `AAᵀ = I ⇒ tr((G')⁻¹) ≤ (n-k+1)(4^k+6k-1)/9` | `TriangularBound.lean` | pivot-Gram trace identity `pivotGram_inv_trace` |

The trace bound is polynomial in `n` but exponential in `k`
(`≈ n·4^k/9`), so it is **not** outcome 1.

Certified witness (`native_decide`, kept in `SmallInstanceChecks.lean`,
not exported as a public structural theorem):

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `frame38_mul_transpose` | `frame38 * frame38ᵀ = 1` (exact, `ℚ`) | `SmallInstanceChecks.lean` | `tests/test_cpqr_r_gt_1.py` |
| `frame38_cpqr_set` | CPQR selects `{0,1,2}` (strict pivot margins) | `SmallInstanceChecks.lean` | same |
| `frame38_inv_norm_lb` | `18‖A_J x‖² < ‖x‖²`, hence `r_CPQR > 1` | `SmallInstanceChecks.lean` | same |

This is a SPEC §9 certification of the `C = 1` case only
(`r_lb ≈ 1.030`, inverse norm `≈ 4.37 ≪ 512 = max(n³, k³,
(k(n-k+1))²)`), so it is **not** outcome 2. The `4×12` record
(`r_CPQR ≈ 1.236`, `experiments/cpqr_r_gt_1_numeric_4_12.json`) is a
float observation and is **not** certified. The Python pipeline that
produced and re-checks these certificates is `structselect.certify`
(`tests/test_certify.py`). Milestone E remains open.

## Thread 5d — Parallel Milestone E merge (not a close)

Formal (proved, default axioms only; none closes E):

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_residual_antitone` | independent `J ⊆ J' ⇒ residualSq A J' ≤ residualSq A J` | `ResidualMono.lean` | projector absorption |
| `milestoneE_residual_insert_downdate` | rank-1 residual downdate on an independent insert | `ResidualMono.lean` | CPQR form `residualSq_cpqr_downdate` |
| `milestoneE_gram_inv_trace_eq_sum_inv_residual` | `tr(G_J⁻¹) = ∑_{j∈J} 1/residualSq A (J.erase j) j` | `SigmaMinBounds.lean` | Cramer's rule / adjugate diagonal |
| `milestoneE_sigma_min_ge_inv_sqrt_trace` | `‖x‖² ≤ ‖A_J x‖² · tr(G⁻¹)` (`σ_min ≥ 1/√tr`) | `SigmaMinBounds.lean` | Cauchy–Schwarz on the inverse Gram |
| `milestoneE_gsR_mul_transpose` | implicit CPQR factor `R Rᵀ = I` | `RowOrthoConstraints.lean` | Parseval pairing of GS directions |
| `milestoneE_bidiagonal_U_inv_trace_le` | bidiagonal `U` `⇒ tr((G')⁻¹) ≤ k(k+1)/2 · (n-k+1)` | `RowOrthoConstraints.lean` | hypothesis on `U`, not a class of `A` |
| `milestoneE_cpqr_inv_energy_le_choose` | `‖x‖² ≤ k C(n,k) ‖A_J x‖²` (exponential / not polynomial) | `StaticClass.lean` | frame23 `25/16 ≤ 6`; frame12 `25/16 ≤ 2` |
| `milestoneE_cpqr_inv_energy_le_of_minDim` | `min(k,n-k)≤d ⇒ ‖x‖² ≤ k n^d ‖A_J x‖²` (Path 3; not Path 1) | `StaticClass.lean` | frame23 `d=1`, `25/16 ≤ 6` |

Numeric (witnesses, not theorems): Path 2 trapezoidal search
(`structselect/adverse.py`,
`experiments/cpqr_adverse_ladder_seed20260816.json`) is
polynomial-looking through `k = 8`. Worst recorded `(8,24)` has
inverse norm `≈ 30.98`, `r_CPQR ≈ 2.66` (`≈ 0.17%` of the named
polynomial). `C = 1` witnesses exist; no superpolynomial family.

## Thread 5e — Path 3 complementary-dimension class

Formal (proved, default axioms only; does not close Path 1):

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_cpqr_inv_energy_le_choose` | `‖x‖² ≤ k C(n,k) ‖A_J x‖²` | `StaticClass.lean` | frame23 `25/16 ≤ 6` |
| `milestoneE_cpqr_inv_energy_le_of_minDim` | `min(k,n-k)≤d ⇒ ‖x‖² ≤ k n^d ‖A_J x‖²` | `StaticClass.lean` | frame23 `d=1` |

ETF / clustered diagnostics:
`experiments/census_static_class_seed1.json`. No new `r_CPQR > 1`.

The dated reasoning log, census labels, and ordered next-work queue
are in `CHECKPOINT.md`. Residual energy and the binomial volume bound
are now proved there as non-polynomial theorems.

Non-claims (intentional):

- no polynomial CPQR inverse-norm bound for general `k`
- no CPQR counterexample past the named polynomial (the certified
  `frame38` witness refutes only the ideal `C = 1` bound)
- no extra static hypothesis that closes Path 1 (the Path 3 class
  `min(k, n-k) ≤ d` is dimensional, not a geometry of `A`)
- no claim that Problem 4.1 is solved
- Python census is a witness, not a source of truth
- `milestoneE_k1_volume_ge` does not close Milestone E
- `milestoneE_cpqr_volume_ge_binomial` is exponential, not polynomial,
  and does not close Milestone E
- `milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`, and
  `milestoneE_last_residual_ge` do not close Milestone E
- `milestoneE_pivot_gram_inv_trace_le` is polynomial in `n` but
  exponential in `k` and does not close Milestone E
- `milestoneE_residual_antitone` and
  `milestoneE_residual_insert_downdate` are projector identities
  and do not close Milestone E
- `milestoneE_gram_inv_trace_eq_sum_inv_residual` and
  `milestoneE_sigma_min_ge_inv_sqrt_trace` are not joint
  `poly(n,k)` bounds and do not close Milestone E
- `milestoneE_gsR_mul_transpose` is `R Rᵀ = I`, not an inverse-norm
  bound
- `milestoneE_cpqr_inv_energy_le_choose` is exponential in `k`
  when `n ≈ 2k` and does not close Milestone E
- `milestoneE_cpqr_inv_energy_le_of_minDim` is a Path 3 theorem
  on `min(k, n-k) ≤ d` and does not close Path 1
- `milestoneE_bidiagonal_U_inv_trace_le` is a hypothesis on
  Gram–Schmidt `U`, not a class of `A`, not Path 1, and not a
  joint `poly(n,k)` theorem
- Path 2 ladder through `k = 8` is polynomial-looking (worst)
  `(8,24)` inverse `≈ 30.98`, `r_CPQR ≈ 2.66`, `≈ 0.17%` of the
  named polynomial); census ratios are witnesses, not theorems

## Phase E column budget — contract (2026-10-23, verified)

Next Path 1 structural slice after the bidiagonal theorem. For real `A :
Matrix (Fin k) (Fin n) ℝ` with `hA : OrthogonalRows A`, assume
`gsUColumnBudget A hA`: for every column `j`,
`∑ l ∈ Iio j, |gsU A hA l j| ≤ 1`.

Named outputs in `ColumnBudget.lean`, re-exported through `Theorems.lean`:
- `milestoneE_column_budget_S_abs_le_one`: every entry of `S=U⁻¹` has
  absolute value at most one, by finite back-substitution.
- `milestoneE_column_budget_inv_trace_le`:
  `tr((pivotGram A hA)⁻¹) ≤ k(k+1)/2 * (n-k+1)`.

This permits multiple predecessors and arbitrarily long edges, unlike
bidiagonal U. Dependencies: existing `gsS_recurrence`, triangular support,
`pivotGram_inv_trace`, and reciprocal residual bounds. Python artifact:
`structselect/column_budget.py`, exact Fraction back-substitution and budget
checks; `tests/test_column_budget.py` independently checks products, trace
closed forms, dense rational examples and a failed weakened hypothesis.
No pivot/selection claims from numerics. Finite deterministic checks only.

Non-claims: budget is an extra hypothesis on CPQR coefficients, not proved
from AAᵀ=I, not a static geometric characterization, not a general CPQR
polynomial theorem, not a solution of Problem 4.1. No volume-sampling changes.
Failed hypothesis to certify: entrywise |U_ij|≤1 alone does not imply the
unit inverse-entry bound (3×3 U with all strict upper entries -1).

Workflow import: GECP reference revision af8b592ca227625aec05e260dbc290bba0261fa2;
all `.agents/skills` copied verbatim. Its CI workflow is preserved as
`.github/workflows/reference/gecp-ci.yml.source`; active CSSP CI uses the
root verify command because GECP module names and dependency commands do
not apply here. Existing unmerged k=2/hygiene work integrated with current
origin/main before this phase; both public tracks and axiom audit retained.

Outcome so far: both named Lean results passed focused elaboration without
placeholders. The failed entrywise-only hypothesis is exactly recertified:
column masses (0,1,2), inverse-column energies (1,2,6), maximum entry 2.
Dense budget examples and chain closed forms pass exact independent tests.
No theorem weakening was needed; the coefficient hypothesis is explicit.
Final root verification and CI status are recorded in README and the PR.

Verification outcome: root `./scripts/verify.sh` passed (70 tests), all 34
public theorem axiom reports use only propext, Classical.choice, Quot.sound,
and CI passed on 13b4d03. Exact chain sums for k=0,1,2,3,8,12 were
independently recomputed as 0,1,3,6,36,78. Final documentation-only revision
is checked by the same root command and CI. Draft PR #13, branch
`codex/phase-e-column-budget`. This phase delivers the proposed conditional
theorem, not a weaker surrogate. Next: identify a geometric sufficient
condition for the budget or a certified frame obstruction to such a condition.

## Goal audit and Phase D actual inverse contract (2026-10-24)

Progress estimate: **45% of the original obligations**, with low confidence in
remaining research effort. The initial 55% estimate counted proxy results too
optimistically. This is not a probability of resolving CPQR. Previous goal turn
was interrupted before actions; this turn revalidated main at 2e691bd and takes
concrete action. Phase column-budget delivery is complete (merged PR #13).

Original obligations, linked to SPEC rather than replaced:
- SPEC §§5–6 and §16 C/D require an actual inverse expectation and inverse-norm
  probability guarantee on every orthogonal-row frame. Existing public names
  prove adjugate proxy identities/tails; the actual-inverse bridge is missing.
  The claimed unconditional expectation equality is false on singular-support
  frames: A=[1,0], k=1,n=2 gives actual expectation 1 versus proxy sum 2.
- SPEC §5 efficient reverse sampler: no sampler exists in structselect; open.
- SPEC §16 E: no general polynomial CPQR theorem or qualifying certified
  obstruction yet; coefficient-budget/min-dimension slices do not close it.
- SPEC §16 F: CSSP norm perturbation bridge is unimplemented; open. Audit and
  delivery interfaces must eventually cover the actual original statements.

Route review: further hypotheses on U do not discharge the missing general
CPQR bridge. Prioritize repairing the randomized theorem's actual semantics,
then investigate new primary CPQR constructions rather than accumulate more
conditional U estimates. A recent primary source (Damle, arXiv:2607.13532,
introduction and bibliography [16]) reports adverse orthogonal-row CPQR examples
and points to Chen et al., arXiv:2606.02484; this is a research lead, not a Lean
certificate. No new CPQR result is claimed in this phase.

Frozen mathematical contract (namespace StructuredColumnSelection):
- Define `selectedInvTrace A J` as the actual inverse column-Gram trace.
  Existing `cols_mul_transpose_inv_trace` identifies it with the row-Gram
  trace on nonsingular k-sets. Sums/events are restricted to those k-sets.
- `milestoneD_actual_expected_inv_trace_le`: AAᵀ=I implies
  ∑_{#J=k} volumeWeight A J * selectedInvTrace A J ≤ k(n+1-k).
- `milestoneD_actual_expected_inv_trace_eq_of_full_support`: the same is an
  equality if every k-column block has nonzero determinant. This extra
  hypothesis is explicit; it does not silently repair the original false type.
- `milestoneD_singular_volume_mass_zero`: singular k-blocks have total mass 0.
- `milestoneD_actual_inv_trace_good_mass`: for δ>0 the mass of nonsingular
  blocks with actual inverse trace ≤ k(n+1-k)/δ is at least 1-δ.
- `milestoneD_actual_inverse_energy_good_mass`: the good event may instead
  require ∀x, ‖x‖² ≤ (k(n+1-k)/δ)‖A_J x‖², an explicit inverse-energy RRQR
  guarantee without a hidden adjugate proxy. No measure-theory/spectral API
  claim; the quadratic bound has its literal finite quantifiers.

Lean target: ActualInverseExpectation.lean, Theorems.lean, AxiomAudit.lean;
public-only expected-type consumers in scripts/CompletionContract.lean.
Independent Python artifact: structselect/volume_exact.py and
 tests/test_volume_exact.py, finite Fraction determinant/solve enumeration,
cofactor recertification and A=[1,0] plus existing frame23 (actual sum=3,
proxy=4) witnesses. Enumeration is an exact verifier, not an efficient sampler.
`milestoneD_actual_expectation_equality_obstruction` is a Lean exact
real-arithmetic witness for A=[1,0], no custom axioms/native_decide
in public structural results. Non-claims: no unconditional equality, efficient
sampler, general CPQR characterization, CSSP bridge, or solution of Problem 4.1.
Success criterion: actual-inverse bounds and finite probability statement,
plus certified failed equality, pass the root command and exact-head CI.

Implementation outcome: the exact five probability/expectation contracts and
one public counterexample are implemented. `selectedInvTrace` uses column
Gram trace (equal to the row-Gram trace on nonsingular square blocks). The
all-frame inverse-energy event explicitly requires nonsingularity and ∀x.
The focused module, including the real-arithmetic counterexample, elaborates.
Sixteen exact tests pass, including full-support frames and extremely small
positive rational masses. No new general matrix expectation equality is claimed.

Estimated completion after this phase: **50%**, conditional on verification
and delivery. This increases from the audited 45% because the actual finite
inverse-energy RRQR obligation is now discharged. It is not based on theorem
or PR counts. Major remaining work: efficient reverse-volume sampling with
exactness/failure evidence, general CPQR proof or certified obstruction,
CSSP perturbation bridge and full original-interface completion audit. These
include research uncertainty; no reliable calendar bound is available.

Next phase selection: implement the missing efficient exact reverse sampler
and prove its finite deletion-weight identity. Continue the CPQR research
route from [Chen et al., §7](https://arxiv.org/html/2606.02484#S7) and
[Damle](https://arxiv.org/html/2607.13532v1), recording explicit n-growth before
claiming a joint-polynomial obstruction. No externally reported result is
counted as a repository theorem.

Original expected type for the §5 scalar expectation (refuted; deliberately
not introduced as a public declaration):
```lean
∀ {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ), OrthogonalRows A →
  (∑ J ∈ (univ : Finset (Fin n)).powersetCard k,
    volumeWeight A J * selectedInvTrace A J) =
      (k : ℝ) * ((n + 1 - k : ℕ) : ℝ)
```
The public counterexample refutes this at k=1,n=2. The public-only contract
consumer for the valid inequality/energy statement has no full-support or
coefficient-budget assumption. PR #14 holds the canonical verification and
merge receipt; phase verification is conditional on the exact checked head.

## Phase D reverse volume sampler (2026-10-24, contract)

Previous goal turn: progress, merged PR #14; exact merge-revision CI passed
at 9d9345e and local/origin main agree. Actual-inverse phase delivery is
complete. Overall estimate remains about 50% before this phase; the efficient
sampler, CPQR characterization and CSSP bridge are still required.

Original obligation: SPEC §5/§14/§20 requires an efficient executable reverse
volume sampler, not an exhaustive verifier or a different pivot mechanism.
Retain the existing finite-distribution inverse-energy theorem from PR #14.
This phase connects reverse deletion to its distribution and supplies a
solve-based rational implementation. It does not close CPQR or CSSP.

Frozen formal contract in `VolumeSampling.lean`, with public aliases in
Theorems.lean and public-only expected-type consumers:
- `retainedVolume A S := ∑ J∈S.powersetCard k, volumeWeight A J`.
- `reverseDeleteProb A S i := retainedVolume A (S.erase i) /
  ((S.card-k) * retainedVolume A S)` (natural subtraction cast to ℝ).
- `milestoneB_reverse_deletion_mass`: sum over i∈S of retainedVolume(S.erase i)
  equals (S.card-k) retainedVolume(S), for k≤S.card.
- `milestoneB_reverse_transition_normalization`: if k<S.card and
  retainedVolume(S)>0, deletion probabilities sum to 1 (and are nonnegative).
- `reverseEndpointMass A r S J` is the literal r-step finite recursion: at
  r=0 the indicator S=J, at r+1 sum_i reverseDeleteProb * child endpoint mass.
- `milestoneD_reverse_sampler_law`: for AAᵀ=I, r=n-k, starting at univ,
  endpoint mass of every J equals volumeWeight A J (zero at wrong cardinality).
  A weighted endpoint invariant on #S=k+r is the proof core, not a replacement
  for this all-frame distribution statement.

Python artifact `structselect/volume_sampling.py`, public `volume_sample`:
exact Parseval rational inputs; uniform rejection while |S|>2k; rational
LDLᵀ downdates; switch to a ≤2k projection Gram block and exact deletion
weights, updated by a rank-one formula. No explicit inverse, floating pivot
or tolerance. Fixed seed/config/revision gives deterministic results. A bounded
proposal budget returns explicit failure without a purported selected sample.
Successful samples include trajectory, arithmetic/certification status and
factorization counters. The ideal transition law is formal; extraction of the
Python program into Lean and random-bit/bit-complexity proofs are non-claims.
Arithmetic work is O(nk²) in expectation for the unbounded hybrid algorithm;
finite counters and exact small-state probability propagation will check the
implemented mechanism. A bounded-failure probability must not be called success.

Independent checks: signed-permutation determinant enumeration on small rational
frames to recompute every transition, propagate the entire finite endpoint law,
check LDLᵀ reconstruction after every downdate, compare dense projection updates
with fresh solves, test zero/tiny weights, repeated columns, seeded byte stability,
and force budget exhaustion. These are exact oracles, not Monte Carlo tests.
No canonical floating experiment or new CPQR selection claim is introduced.

Literature gate: Dereziński–Warmuth, Reverse iterative volume sampling,
[§5](https://arxiv.org/html/1806.01969), describes hybrid rejection followed by a
small dense finish. We adapt the mechanism to factor/solve arithmetic rather
than storing an explicit inverse. No novelty claim. Before implementing local
finite combinatorics, search mathlib and record candidates in MATHLIB.md.

Backend bridge refinement before implementation: also prove
`milestoneB_retained_volume_eq_det_gram` using Cauchy–Binet on zeroed-out
columns, and `milestoneB_reverse_score_eq_volume_ratio` for the actual solve
score 1-aᵢᵀG_S⁻¹aᵢ. Its [0,1] bounds justify rejection sampling. These results
connect the efficient backend's matrix quantities to the finite kernel, rather
than rely on tests alone for that conceptual identification. Python LDLᵀ and
dense-update code is not formally extracted; it is independently recertified.

Proof-development checkpoint: the endpoint law compiled before the backend
bridge. Matrix notation/simplification attempts at the determinant lemma
exposed a 1×1 reduction issue, isolated as the precise helper obligation
`det(1 + row(v) * M⁻¹ * col(-v)) = 1 - vᵀ M⁻¹ v`. Use mathlib's determinant
lemma plus `replicateCol_mulVec`/`mulVec_mulVec`; no new hypothesis or weakened
sampler statement is introduced. The issue is a typed matrix reduction, not a
counterexample to the deletion law. The rational backend tests already include
full LDLᵀ reconstruction and independent determinant ratios at each deletion.

Next decision after verified delivery: pursue a concrete wide-frame CPQR
completion construction, rather than more sufficient hypotheses on U. Candidate
parameters (not yet a theorem/counterexample): k=m², ε=(4m²-1)/(4m²+1),
s=4m/(4m²+1), c=s/2, α=1/(2k), and an upper-triangular selected block with
diagonal αε^i and strict-upper entries -cαε^i. Complete I-RRᵀ by a PSD square
root, then split each completion column into t=32k² copies scaled by 1/√t.
The proposed ambient width is n=k+32k³, explicitly polynomial in k. The
research obligations are strict pivot order for every prefix, exact Parseval
completion, and a quantitative inverse-entry amplification bound. Test those
claims exactly before any outcome-2 claim. This adapts the prescribed-block
completion idea from Chen et al.; no new novelty or CPQR conclusion is claimed
by this sampler phase. CSSP and the remaining application comparison API are
still separate obligations.

Implementation status: the backend Gram/score bridge and literal endpoint law
pass focused Lean elaboration. Successful samples now also carry an exact
inverse trace, computed one solve RHS at a time. A CLI emits canonical seeded
records with source/input hashes and Python version. Twenty-three focused tests
pass; the public exports and full root gates are next. Estimated completion
after verified delivery: about 60%, reflecting the executable sampler and its
distribution/conditioning link, not theorem or PR counts. Remaining research
work is uncertain. No failed mathematical hypothesis was needed in this phase;
the backend reduction hurdle was resolved without weakening the contract.

Canonical verification and authorized merge evidence for this phase are on
PR #15. The source status remains implemented until that receipt proves the
final revision passed the root command, exact-head CI, merge and main checks.

## Phase E wide-frame CPQR obstruction (2026-10-24, initial research contract)

Previous goal turn: progress; PR #15 merged at b654abb, exact main CI passed
and local/origin main agree. Reverse-sampling phase delivery is complete.
Overall estimate remains about 60%; no new CPQR conclusion is counted yet.

Original SPEC §16 E obligation remains a general polynomial theorem, a
qualifying certified obstruction, or a counterexample plus a stronger class.
This phase targets an actual orthogonal-row adverse family, not another U-only
sufficient hypothesis. SPEC §9 requires exact row orthogonality, every pivot,
and an inverse-norm/energy lower bound. CPQR and randomized results stay separate.

Frozen candidate, with conservative polynomial padding: m≥2, k=m²,
ε=(4m²-1)/(4m²+1), c=2m/(4m²+1), α=1/(2k), dᵢ=αεⁱ.
R is upper triangular, Rᵢᵢ=dᵢ and Rᵢⱼ=-c dᵢ for i<j. Complete
I-RRᵀ=C Cᵀ using mathlib positive-semidefinite factorization and split each
column of C into t=32k³ copies scaled by 1/√t. Thus n=k+32k⁴. The earlier
n=k+32k³ route would require a per-column bound ≤1 for a principal square root;
we instead use the elementary total-energy bound ≤k for a generic factor.
This changes a proof-route degree, not the joint-polynomial obstruction target.

Target Lean modules: WideCPQR.lean (generic completion/prefix pivot facts),
WideCPQRFamily.lean (parameters, exact triangular witness, quantitative rate).
Public targets, exported through Theorems.lean with expected-type consumers:
- `milestoneE_wide_completion_orthogonal`: small-Frobenius R admits the stated
  finite padded orthogonal-row completion, with original columns unchanged.
- `milestoneE_triangular_prefix_pivots`: an upper-triangular leading block with
  strict tail-energy pivot dominance and smaller completion columns is selected
  by the actual `cpqrIterate`/`cpqrSet` implementation. The hypotheses concern
  finite entries/energies, not the asserted pivot sequence.
- `milestoneE_wide_adverse_family`: for every m≥2 an actual completed frame at
  polynomial width, the certified first-k pivot set, and an explicit inverse
  energy witness growing at least geometrically in m. Proposed lower scale is
  (2m/3)(4/3)^(m-1), to be checked before any rate claim.
- Intended close `milestoneE_cpqr_no_joint_polynomial`: for every natural d and
  C>0, some orthogonal-row frame and nonzero selected-coordinate x satisfy
  C(n+k+1)^(2d) energy(A_selected x) < energy(x). Do not claim this theorem
  unless the actual full statement is proved; a weaker output must be named
  precisely and leave E open.

Small exact core first: prefix projectors are coordinate truncations; leading
triangular columns have strict residual dominance; PSD completion gives small
filler columns; back-substitution supplies a rational witness. The finite
parameter/growth bounds precede any asymptotic language. Search mathlib first.

Independent Python target `structselect/wide_cpqr.py` and exact tests: bounded
rational R and LDLᵀ completion certificates; symbolic columns L(:,j)√(Dⱼ/t)
with rational pair products; exact row-Gram reconstruction and all prefix
residual comparisons; solve-based inverse-energy witness. Large dimensions
must remain compressed. Parameter-only bounds are labeled as such, not a full
materialized matrix certificate; budget exhaustion is explicit. No floating
pivot decision or explicit inverse is permitted.

Non-claims until completion: no qualifying CPQR counterexample, polynomial
upper bound, leverage/coherence theorem, CSSP bridge or solution of all Problem
4.1. The prescribed-block completion route is informed by Chen et al.,
[§7](https://arxiv.org/html/2606.02484#S7), without a novelty claim. If a planned
rate/hypothesis fails, preserve the exact failed case and deliver only a named
weaker theorem or certified obstruction. Do not replace the endpoint with a
conditional or tautological wrapper.

### Bounded delivery contract — completion and prefix core

The request to commit and merge the current local work closes this phase at
the exact algebraic core. The full adverse family and no-joint-polynomial
statement above are **not delivered**. Milestone E and SPEC §9's qualifying
obstruction remain open; the overall estimate stays about 60%. This is a named
weaker result, not an outcome-2 certificate or a revised original SPEC goal.

Delivered public types (all matrices are real and finite):
- `milestoneE_wide_completion_orthogonal`: for every square k×k R with
  `frobEnergy R ≤ 1` and every natural t>0, there exists k×(k+k*t) A with
  `OrthogonalRows A`, first k columns exactly R, and each remaining column's
  energy ≤ k/t. This includes k=0; no triangular or invertibility assumption.
- `milestoneE_triangular_prefix_projector`: for every k≤n and k×n A whose
  first k columns are upper triangular with nonzero diagonal, every t≤k has
  nonsingular selected-column Gram on `widePrefix n t`, and its projector
  sends every x to `prefixCut t x`. No row-orthogonality assumption is needed.
- `milestoneE_triangular_prefix_residual`: under the same entry hypotheses,
  every column j and t≤k satisfy `residualSq A (widePrefix n t) j =
  tailEnergy t (A.col j)`.
- `milestoneE_triangular_prefix_pivots`: additionally assume, for every p<k
  and j>p, `tailEnergy p (A.col j) < A p (Fin.castLE hkn p)^2`.
  Then every t≤k satisfies `cpqrIterate A t = widePrefix n t`. The strict
  inequalities are entry/tail-energy hypotheses, not a pivot-sequence premise.
- `milestoneE_wide_parameter_diagonal_lower`: for every natural m≥2 and
  i<m², `wideAlpha m / 2 < wideDiagNat m i`, with the rational parameters
  in the initial contract. It does not assert a completed-family pivot law.

Implementation: `WideCPQR.lean`, `WideCPQRParameters.lean`, public exports in
`Theorems.lean`, audit declarations, and literal consumers in
`scripts/CompletionContract.lean`. The downstream consumer is the proposed
family: instantiate the triangular tail inequalities, prove its Frobenius
bound, transport the selected coordinates, and establish inverse growth.
Those bridges and the all-polynomial quantifier remain outstanding.

Independent Python evidence: `structselect/wide_cpqr.py` gives bounded exact
compressed algebraic checks; `tests/test_wide_cpqr.py` uses bordered-Gram
determinant ratios computed by row elimination, not the coordinate-tail rule
or LDL solve. It checks every prefix for m=2,3, all symbolic completion pair
products, closed-form witnesses for m=2,3,4, deterministic bytes, invalid
inputs and factor/budget failures. Scalar-only checks at m=2,64,1024 remain
explicitly separate from frame certification. No explicit inverse is formed.

Failed/unsupported hypotheses: no mathematical counterexample to these core
lemmas was found. A unit-column bound on an arbitrary completion factor was
not established by this proof route; the delivered theorem uses the proved
total-energy bound k and padding 32k³. The proposed amplification bound has
small-instance evidence, not an all-m theorem. Earlier unfinished proof errors
were elaboration/algebra errors, not evidence refuting the family. No joint
CPQR obstruction, polynomial upper bound, CSSP bridge or Problem 4.1 solution
is claimed. Verification and delivery are recorded in the phase PR receipt.

Workflow synchronization: upstream GECP main was checked at
`f06a46300156ce2f645fa3413a7919f8e1b81229`. All four imported skill/reference
blobs and the saved CI workflow source match that revision exactly; no newer
skill content needed copying. CSSP bindings remain in `.agents/WORKFLOW_IMPORT.md`.

## Phase E explicit adverse family (2026-10-24, contract)

Previous turn: progress. PR #16 is merged at 410d51a; main CI passed and the
local tree is clean. Its algebraic core is complete; this phase consumes it.
Original SPEC §9 / §16 E scope and the proposed no-joint-polynomial type above
are retained. Remaining original obligations keep the estimate near 60%.

Target `WideCPQRFamily.lean` and `WideCPQRGrowth.lean`, re-exported/audited with
public-only literal consumers:

- `milestoneE_wide_adverse_family`: for every natural m≥2, k=m² and
  n=k+32k⁴, there exists an actual real k×n Parseval frame A whose CPQR set is
  the first k indices, whose leading block is `wideTriangular m`, and an
  explicit nonzero selected-coordinate vector with inverse-energy ratio at
  least `((2m/3)*(4/3)^(m-1))²`. No tail-dominance or factor assumption is
  left on the public statement.
- `milestoneE_cpqr_no_joint_polynomial`: for every d:ℕ and C>0, some real
  orthogonal-row frame A and selected-coordinate x satisfy
  `C*(n+k+1)^(2*d)*vecEnergy(selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x`.
  This quantifies actual CPQR selections, not an arbitrary triangular factor.

Small exact core: instantiate the Frobenius and strict tail-energy conditions,
then use the already-proved completion and prefix law. Prove a finite geometric
sum for the explicit triangular witness and an explicit growth lower bound
before using geometric-over-polynomial limits. The observable route criterion
is the all-m frame/pivot theorem; if it fails, isolate the exact missing bridge
or independently recertified failure instead of adding another unused layer.

Independent Python: retain the existing compressed determinant oracle. Extend
`wide_cpqr.py` / `tests/test_wide_cpqr.py` only where the new finite growth
certificate needs evidence: independently recompute the geometric witness,
quantitative lower scale, and any explicit threshold; keep scalar-only checks
distinct from whole-frame checks, with fixed deterministic inputs and explicit
budget failures. No explicit inverse or floating pivot claim.

Non-claims: no polynomial CPQR upper bound, no CSSP theorem, no conclusion for
all of Simons Problem 4.1, no novelty claim for prescribed-block completion,
and no replacement of the randomized result by the CPQR obstruction. A full
qualifying obstruction requires both the actual-family and all-polynomial
quantifiers; finite scalar crossings alone do not close E.

## Phase E explicit adverse family (2026-10-29, delivery)

`milestoneE_wide_adverse_family` proves, for every natural `m ≥ 2`, an
orthogonal-row frame of width `k + 32 k⁴` with `k = m²`, leading block
`wideTriangular m`, CPQR set equal to the first `k` indices, a selected
coordinate of image energy `1`, and inverse energy at least
`((2m/3)(4/3)^(m-1))²`. `milestoneE_cpqr_no_joint_polynomial` consumes that
family: for every degree `d` and every `C > 0`, some actual CPQR block
satisfies `C(n+k+1)^{2d} ‖A_J x‖² < ‖x‖²`.
`milestoneE_cpqr_named_polynomial_obstruction` instantiates `d = 4` and
`C = 1`, which puts the squared inverse energy above
`max(n³, k³, (k(n-k+1))²)²`. This closes outcome 2 only. It is not a
polynomial bound for every orthogonal-row matrix, not outcome 3, and not a
CSSP theorem. The randomized quasi-optimal sentence stays in force. Problem
4.1 is not claimed solved.

Independent check: `tests/test_wide_cpqr.py` recomputes bordered-Gram
residuals, multiplies the closed-form witness, and cross-multiplies the
closed head against the scale at `m = 2, 3, 4`. Scalar
`growth_parameters` stays `frame_certified = False`.

Phase PR and verification receipt:
[#18](https://github.com/tripp-smith/structured-column-selection/pull/18).

## Phase F CSSP bridge (2026-10-29, contract)

Target `StructuredColumnSelection/CSSPBridge.lean`, re-exported and audited:

- `milestoneF_cssp_spectral`
- `milestoneF_cssp_frobenius`

For `A = U S Qᵀ + E` with `Qᵀ Q = 1`, and a column index set `J` of size `k`
whose row submatrix `Q_J` is invertible, set `T = (Q_Jᵀ)⁻¹ Qᵀ`. Both theorems
state

`‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖`

with the left-hand norm spectral in the first theorem and Frobenius in the
second. The coefficient on the right is the spectral norm in both. This is
the SPEC §11 comparison for a supplied orthonormal factor. It does not
construct a truncated SVD.

Independent check: `tests/test_cssp_bridge.py` recomputes
`A - A_J T = E - E_J T` in exact rationals and compares squared Frobenius
energy with `(1 + |q|⁻¹)²` on one fixed rank-1 example. No floating pivot.

Non-claims: no polynomial bound for every orthogonal-row matrix, no outcome 3
static class, no replacement of the randomized theorem, and no claim that
Problem 4.1 is solved.

Delivered: `milestoneF_cssp_spectral` and `milestoneF_cssp_frobenius` are
the statements in the contract. Both call the coefficient identity
`A - A_J T = E - E_J T`. The factor `Q` is supplied; the proof does not
construct a truncated SVD. The exact Python check is the rank-1 identity
in `tests/test_cssp_bridge.py`. It is not the theorem.

Phase PR and verification receipt:
[#19](https://github.com/tripp-smith/structured-column-selection/pull/19).

## Phase G wide leverage escape (2026-10-29, contract)

Iteration G of the long-horizon cadence. Outcome 1 is not the target:
`milestoneE_cpqr_no_joint_polynomial` already says no single polynomial
bounds every orthogonal-row matrix. Outcome 3 stays open. This phase does
not close it.

Route checkpoint. Sequential CPQR residuals are at least `(k-#J)/(n-#J)`
(`milestoneE_next_residual_ge`), which recovers only the binomial volume
bound. Inverse trace is a sum of leave-one-out residuals
(`milestoneE_gram_inv_trace_eq_sum_inv_residual`). A leverage-ratio class
can exclude the outcome-2 family only if that family's column-energy ratio
is unbounded. Exact compressed energies at `m = 2, 3, 4` sit just above
`8 m²`. The proof uses the average filler energy, not those explicit
LDL values.

Target in `StructuredColumnSelection/WideLeverage.lean`, re-exported as
`milestoneE_wide_leverage_escape`: for every `τ ≥ 0` there is an `m ≥ 2`
and a frame from `wide_adverse_family` with two columns whose empty
residuals `e_min`, `e_max` satisfy `τ e_min < e_max`. The ratio is at
least `8 m²`.

Independent check: `tests/test_wide_leverage.py` recomputes triangular
column energies and LDL completion-column energies at `m = 2, 3, 4` and
checks that their max/min is at least `8 m²`. Float prints are not the
proof.

Non-claims: no polynomial inverse bound under a leverage-ratio hypothesis,
no coherence theorem, no closure of outcome 3, and no claim that Problem
4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#20](https://github.com/tripp-smith/structured-column-selection/pull/20).

## Phase H inverse-trace step (2026-10-29, contract)

Iteration H. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Standard CPQR maximizes the residual denominator.
The inverse-trace increment of an appended column is
`(1 + ‖G⁻¹ Bᵀ v‖²) / residual`, so the numerator can make a large-residual
column a bad pivot. The minimizing choice of that whole ratio is a
different rule. Phase G already shows the outcome-2 family leaves every
fixed leverage ratio; it does not bound this numerator. The consumer of
the increment identity is a later induction for the minimizing rule.
That induction is not this phase.

Target in `StructuredColumnSelection/InvTraceStep.lean`, re-exported
from `Theorems.lean`:

- `milestoneE_append_inv_trace_increment`: if `Bᵀ B` is invertible and the
  Schur residual of `v` is nonzero, the inverse trace of
  `(appendColumn B v)ᵀ (appendColumn B v)` equals the inverse trace of
  `Bᵀ B` plus `(1 + ‖(Bᵀ B)⁻¹ (Bᵀ v)‖²) / residual`.

The comparison that some unused column meets
`((n - t) + trace(G⁻¹) - t) / (k - t)` is the next phase, not this one.

Independent check: `tests/test_inv_trace_step.py` recomputes the `2×2`
Gram inverse trace of columns `{0,1}` of the rational `2×3` frame
`[[1,0,0],[0,3/5,4/5]]` and compares it with `1 + 25/9`. It does not
call the CPQR residual code. It is not the theorem.

Non-claims: no polynomial CPQR bound, no claim that the max-residual
pivot obeys the same increment estimate, no closure of outcome 3, and
no claim that Problem 4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2`
stay outside outcome 3.

Phase PR and verification receipt:
[#21](https://github.com/tripp-smith/structured-column-selection/pull/21).

## Phase I best-column increment (2026-10-29, contract)

Iteration I. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Phase H identifies the inverse-trace increment as
`(1 + ‖G⁻¹ Bᵀ a_j‖²) / residualSq`. Standard CPQR does not minimize that
ratio. The bound below is the comparison a minimizing rule would use. It
is not yet that rule, and it is not an induction.

Target in `StructuredColumnSelection/BestColumnIncrement.lean`, re-exported
as `milestoneE_best_column_increment_le`: for orthogonal rows, an
invertible selected Gram, and `t = #J < k`, some column outside `J` has
positive residual and
`(1 + ‖G⁻¹ Bᵀ a_j‖²) / residual ≤ ((n - t) + trace(G⁻¹) - t) / (k - t)`.

Independent check: `tests/test_best_column_increment.py` uses the rational
`2×3` frame and `J = {0}`. Column 2 has ratio `25/16`, and the comparison
is `2`. It does not call CPQR. It is not the theorem.

Non-claims: no polynomial CPQR bound, no claim that the max-residual pivot
meets the estimate, no closure of outcome 3, and no claim that Problem
4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#22](https://github.com/tripp-smith/structured-column-selection/pull/22).

## Phase J inverse-trace growth step (2026-10-29, contract)

Iteration J. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Phase I supplies a column whose inverse-trace increment
is at most `((n - t) + trace(G⁻¹) - t) / (k - t)`. Phase H turns that
increment into the trace of the appended Gram. The one-step consequence is
that a block whose inverse trace is already at most
`t (n - t + 1) / (k - t + 1)` can be extended by one column so the new
inverse trace is at most `(t + 1) (n - t) / (k - t)`. Carrying the
induction from the empty set through `k` columns is the next phase, not
this one. The pivot is not max-residual CPQR.

Target in `StructuredColumnSelection/InvTraceGrowth.lean`, re-exported as
`milestoneE_inv_trace_growth_step`: for orthogonal rows, an invertible
selected Gram, `t = #J < k`, and
`trace(G⁻¹) ≤ t (n - t + 1) / (k - t + 1)`, some column outside `J`
makes the appended Gram inverse trace at most
`(t + 1) (n - t) / (k - t)`.

Independent check: `tests/test_inv_trace_growth.py` appends column 2 of
the rational `2×3` frame to column 0. The `1×1` trace is `1`, which is at
most `3/2`, and the appended `2×2` inverse trace is `1 + 25/16`, which is
at most `4`. It does not call CPQR. It is not the theorem.

Non-claims: no polynomial CPQR bound, no claim that the max-residual pivot
obeys the step, no closure of the induction, no closure of outcome 3, and
no claim that Problem 4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2` stay
outside outcome 3.

Phase PR and verification receipt:
[#23](https://github.com/tripp-smith/structured-column-selection/pull/23).

## Phase K inverse-trace induction (2026-10-29, contract)

Iteration K. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Phase J is one growth step for a block that already
meets `t (n - t + 1) / (k - t + 1)`. The empty Gram has inverse trace
`0`, which meets the `t = 0` case. Iterating the step through `k`
columns produces a `k`-set whose inverse trace is at most
`k (n - k + 1)`. The column at each step meets the phase-I increment
bound. It is not the max-residual CPQR pivot. The spectral norm bound is
a later phase.

Target in `StructuredColumnSelection/InvTraceInduction.lean`, re-exported
as `milestoneE_minimizing_inv_trace_le`: for orthogonal rows, some
`J` with `#J = k` has invertible selected Gram and
`trace(G⁻¹) ≤ k (n - k + 1)`.

Independent check: `tests/test_inv_trace_induction.py` inverts the Gram
of columns `{0, 2}` of the rational `2×3` frame by cofactors. The trace
is `1 + 25/16`, and `k (n - k + 1) = 4`. It does not call CPQR. It is
not the theorem.

Non-claims: no polynomial CPQR bound, no claim that CPQR selects this
set, no spectral-norm bound, no closure of outcome 3, and no claim that
Problem 4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#24](https://github.com/tripp-smith/structured-column-selection/pull/24).

## Phase L inverse spectral bound (2026-10-29, contract)

Iteration L. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Phase K produces a `k`-set with
`trace(G⁻¹) ≤ k (n - k + 1)`. Every column submatrix of an
orthogonal-row matrix is a contraction, so `G⁻¹ - I` is positive
semidefinite and the largest Rayleigh quotient of `G⁻¹` is at most
`trace(G⁻¹) - (k - 1)`. That quantity is at most `1 + k (n - k)`.
Success is the public squared-energy inequality below. Exit if the
contraction fails to make `G⁻¹ - I` positive semidefinite, or if the
trace subtraction does not reach `1 + k (n - k)`.

Target in `StructuredColumnSelection/InvSpectralBound.lean`, re-exported
as `milestoneE_minimizing_inv_spectral_le`: for orthogonal rows, some
`J` with `#J = k` has invertible selected Gram and
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²` for every coefficient vector `x`.

Independent check: `tests/test_inv_spectral_bound.py` multiplies columns
`{0, 2}` of the rational `2×3` frame by `(0, 1)`. The image energy is
`16/25`, and `1 + k (n - k) = 3`. It does not call CPQR. It is not the
theorem.

Non-claims: no polynomial CPQR bound, no claim that CPQR selects this
set, no closure of outcome 3, and no claim that Problem 4.1 is solved.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#25](https://github.com/tripp-smith/structured-column-selection/pull/25).

## Phase M increment set (2026-10-29, contract)

Iteration M. Outcome 3 stays open. Outcome 1 is not the target.

Route checkpoint. Phases K and L prove that some column sequence meeting
the increment bound has inverse trace at most `k (n - k + 1)` and
squared inverse operator norm at most `1 + k (n - k)`. The max-residual
rule is a different pivot. This phase names the least-index minimizer of
the increment `(1 + ‖G⁻¹ Bᵀ a_j‖²) / residual` and proves the bounds for
that set. Success is `milestoneE_increment_set_bound`. Exit if the
least-index minimizer fails the average comparison that phase I proves
for some column.

Target in `StructuredColumnSelection/IncrementSet.lean`, re-exported as
`milestoneE_increment_set_bound`: for orthogonal rows, `incrementSet A`
has cardinality `k`, invertible selected Gram, inverse trace at most
`k (n - k + 1)`, and `‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

Independent check: `tests/test_increment_set.py` computes the empty-block
scores `1`, `25/9`, and `25/16` on the rational `2×3` frame, then the
Schur scores after column 0. The least index of the minimum is column 0
and then column 2. The Gram inverse trace of those columns is
`1 + 25/16`, which is at most `4`. It does not call CPQR. It is not the
theorem.

Non-claims: no polynomial CPQR bound, no claim that this pivot is
max-residual CPQR, no closure of outcome 3, and no claim that
Problem 4.1 is solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#26](https://github.com/tripp-smith/structured-column-selection/pull/26).

## Phase N pivot split (2026-10-29, contract)

Iteration N. Outcomes 1 and 3 stay open.

Route checkpoint. Phase M names the least-index minimizer of the
inverse-trace increment and proves its inverse-trace and squared
spectral bounds. Those statements do not identify the pivot with
max-residual CPQR. This phase separates the two rules on one explicit
orthogonal-row frame. Success is `milestoneE_increment_set_ne_cpqr`.
Exit if every orthogonal-row matrix that was checked gives the same set
for both rules, or if the separation needs `native_decide`.

Target in `StructuredColumnSelection/PivotSplit.lean`, re-exported as
`milestoneE_increment_set_ne_cpqr`: there is an orthogonal-row `2×5`
matrix with `incrementSet A ≠ cpqrSet A`. The witness is `(1/4)` times
the integer rows `(1, -3, -2, -1, -1)` and `(-3, 1, -2, -1, -1)`. Both
rules take column `0` first. CPQR then takes column `1`. The increment
pivot takes column `2`.

Independent check: `tests/test_pivot_split.py` recomputes the row Gram,
the five column energies, the four residuals after column `0`, and the
four increment ratios from the entries with rational arithmetic. The
CPQR index is `1` and the increment index is `2`. It does not call the
repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound, no closure of outcome 1 or
outcome 3, and no claim that Problem 4.1 is solved. The `2×5` witness
is a separation of two pivots. `k = 2` stays outside outcome 3.
`MinDimLe` stays outside outcome 3.

Phase PR and verification receipt:
[#27](https://github.com/tripp-smith/structured-column-selection/pull/27).

## Phase O zero-coefficient pivot (2026-10-29, contract)

Iteration O. Outcomes 1 and 3 stay open.

Route checkpoint. Phase N shows that a nonzero coefficient can make
the increment pivot and max-residual CPQR select different columns.
This phase proves the complementary step: a zero coefficient makes the
increment the reciprocal of the residual, so the two least-index rules
return the same column. Success is `milestoneE_zero_coeff_same_pivot`.
Exit if a zero coefficient still leaves the argmin of the ratio
different from the argmax of the residual.

Target in `StructuredColumnSelection/ZeroCoeffPivot.lean`, re-exported
as `milestoneE_zero_coeff_same_pivot`: when the selected Gram is
invertible and every positive-residual unused column has coefficient
zero, `incrementPivot A J = cpqrPivot A J`.

Independent check: `tests/test_zero_coeff_pivot.py` recomputes the
rational `2×3` frame. Column 0 is orthogonal to columns 1 and 2, the
residuals are `9/25` and `16/25`, and both least-index scores pick
column 2. It does not call the repository CPQR code. It is not the
theorem.

Non-claims: no polynomial CPQR bound, no claim that the rules agree on
every orthogonal-row matrix, no closure of outcome 1 or outcome 3, and
no claim that Problem 4.1 is solved. Phase N remains the separation.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#28](https://github.com/tripp-smith/structured-column-selection/pull/28).

## Phase P orthogonal-column CPQR (2026-10-29, contract)

Iteration P. Outcomes 1 and 3 stay open.

Route checkpoint. Phases H–O compare the inverse-trace increment with
max-residual CPQR. Another pivot-agreement lemma would not discharge
outcome 3. This phase proves a CPQR bound on a static class:
`ColumnIncoherent A 0`, pairwise orthogonal columns. With orthogonal
rows, every column energy is `0` or `1`, exactly `k` columns have
energy `1`, and max-residual CPQR selects them. Their Gram is the
identity. Success is `milestoneE_incoherent_zero_cpqr_bound`. Exit if
an unused energy-`1` column can have a nonzero coefficient against the
selected block.

Target in `StructuredColumnSelection/OrthogonalColumns.lean`, re-exported
as `milestoneE_incoherent_zero_cpqr_bound`: for `OrthogonalRows A` and
`ColumnIncoherent A 0`, the CPQR set has cardinality `k`, invertible
Gram, inverse trace at most `k (n - k + 1)`, and
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`.

Independent check: `tests/test_orthogonal_columns.py` recomputes the
`2×4` partial permutation. Off-diagonal column dots are `0`, energies
are `1, 1, 0, 0`, both scores select `{0, 1}`, and the inverse trace
`2` is at most `k (n - k + 1) = 6`. It does not call the repository
CPQR code. It is not the theorem.

Non-claims: this does not close outcome 1 or outcome 3.
`ColumnIncoherent A 0` is read from `A` and is checkable, but it is
stricter than the weakest SPEC §10 class. The adverse family is not
incoherent at `0`. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3. Problem 4.1 is not solved.

Phase PR and verification receipt:
[#29](https://github.com/tripp-smith/structured-column-selection/pull/29).

## Phase Q adverse family outside orthogonal columns (2026-10-29, contract)

Iteration Q. Outcomes 1 and 3 stay open.

Route checkpoint. Phase P bounds max-residual CPQR on
`ColumnIncoherent A 0`. That class is too narrow to close outcome 3.
This phase shows the outcome-2 frame is outside it. Success is
`milestoneE_wide_not_incoherent_zero`. Exit if the leading triangular
columns of that frame are orthogonal.

Target in `StructuredColumnSelection/WideIncoherent.lean`, re-exported
as `milestoneE_wide_not_incoherent_zero`: for every `m ≥ 2` there is an
orthogonal-row matrix of the outcome-2 shape with
`¬ ColumnIncoherent A 0`. The leading columns have inner product
`-wideC m * (wideDiagNat m 0) ^ 2`.

Independent check: `tests/test_wide_incoherent.py` recomputes that
scalar for `m = 2` as `-(4/17) * (1/8)^2`. It does not call the
repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound on a SPEC §10 class, no closure
of outcome 1 or outcome 3, and no claim that Problem 4.1 is solved.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#30](https://github.com/tripp-smith/structured-column-selection/pull/30).

## Phase R equal-energy second pivot (2026-10-29, contract)

Iteration R. Outcomes 1 and 3 stay open.

Route checkpoint. Equal column energy is leverage ratio `1`, the balanced
end of the SPEC §10 leverage-ratio candidate. A direct induction with
`‖G⁻¹ v‖² ≤ trace(G⁻¹) · q` unrolls exponentially, so this phase does not
claim a `k`-set bound. Success is the second pivot only:
`milestoneE_equal_energy_cpqr_prefix_trace`. Exit if the one-column ratio
is not monotone in the residual.

Target in `StructuredColumnSelection/EqualEnergyPivot.lean`, re-exported
as `milestoneE_equal_energy_cpqr_prefix_trace`: if the rows are orthogonal,
every column energy is equal, `2 ≤ k`, and `0 < n`, then each energy is
`k / n`, the first CPQR pivot is column `0`, the second CPQR pivot equals
the increment pivot, and the two-column inverse trace is at most
`2 (n - 1) / (k - 1)`.

Independent check: `tests/test_equal_energy_pivot.py` uses exact
arithmetic on the rational `2×4` frame with entries `±1/2`. Both scores
select column `0`, then column `1`, and the inverse trace is `4 ≤ 6`.
It does not call the repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound for every equal-energy matrix when
`k > 2`, no closure of outcome 1 or outcome 3, and no claim that
Problem 4.1 is solved. Equal energy is stricter than the weakest SPEC §10
class. The outcome-2 family is outside it. When `k = 2` the two-column
bound is `k (n - k + 1)`, and that still does not close outcome 1 or 3.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#31](https://github.com/tripp-smith/structured-column-selection/pull/31).

## Phase S equal-energy prefix Rayleigh (2026-10-29, contract)

Iteration S. Outcomes 1 and 3 stay open.

Route checkpoint. Phase R's estimate `‖G⁻¹ v‖² ≤ trace(G⁻¹) · q` does not
close pivots after the second. At the two-column prefix the smaller
eigenvalue is available: the second residual is at least `(k - 1) / (n - 1)`,
and `e - |s|` is at least half that residual. Success is that Rayleigh
lower bound only: `milestoneE_equal_energy_cpqr_prefix_rayleigh`. Exit if
the second pivot residual is below the unused average, or if `e - |s|`
is below half the residual.

Target in `StructuredColumnSelection/EqualEnergyPivot.lean`, re-exported
as `milestoneE_equal_energy_cpqr_prefix_rayleigh`: if the rows are
orthogonal, every column energy is equal, `2 ≤ k`, and `0 < n`, then for
every coefficient vector on the CPQR two-column set,
`((k - 1) / (2 (n - 1))) ‖x‖² ≤ ‖A_J x‖²`.

Independent check: `tests/test_equal_energy_pivot.py` uses exact
arithmetic on the rational `2×4` frame. Columns `{0, 1}` have inner
product `0` and energy `1/2`, so the image energy of `(3, 4)` is `25/2`,
and `(k - 1) / (2 (n - 1)) = 1/6`. It does not call the repository CPQR
code. It is not the theorem.

Non-claims: no polynomial CPQR bound for every equal-energy matrix when
`k > 2`, no finished induction from `c ≤ q / λ_min`, no closure of
outcome 1 or outcome 3, and no claim that Problem 4.1 is solved. Equal
energy is stricter than the weakest SPEC §10 class. The outcome-2 family
is outside it. When `k = 2` the phase-R trace bound is
`k (n - k + 1)`, and that still does not close outcome 1 or 3.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#32](https://github.com/tripp-smith/structured-column-selection/pull/32).

## Phase T equal-energy three-column trace (2026-10-29, contract)

Iteration T. Outcomes 1 and 3 stay open.

Route checkpoint. Phase S bounds the two-column Rayleigh quotient so that
`‖G⁻¹ v‖² ≤ q / λ_min` at that prefix. The consumer is one CPQR step:
the third-column inverse-trace increment is `(1 + ‖G⁻¹ v‖²) / residual`,
the residual is at least `(k - 2) / (n - 2)`, and `‖G⁻¹ v‖²` is at most
`(k / n) / λ_min`. Success is that three-column trace bound only:
`milestoneE_equal_energy_cpqr_three_trace`. Exit if the third residual is
below the unused average, or if the coefficient exceeds `(k / n) / λ_min`.

Target in `StructuredColumnSelection/EqualEnergyPivot.lean`, re-exported
as `milestoneE_equal_energy_cpqr_three_trace`: if the rows are orthogonal,
every column energy is equal, `3 ≤ k`, and `0 < n`, then the CPQR
three-column Gram is invertible and its inverse trace is at most
`2 (n - 1) / (k - 1)` plus
`(1 + 2 k (n - 1) / (n (k - 1))) · (n - 2) / (k - 2)`.

Independent check: `tests/test_equal_energy_three.py` uses exact
arithmetic on the `3×3` identity. The inverse trace is `3` and the bound
is `5`. It does not call the repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound for every equal-energy matrix when
`k > 3`, no finished induction, no closure of outcome 1 or outcome 3, and
no claim that Problem 4.1 is solved. Equal energy is stricter than the
weakest SPEC §10 class. The outcome-2 family is outside it.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#33](https://github.com/tripp-smith/structured-column-selection/pull/33).

## Phase U equal-energy three-row CPQR (2026-10-29, contract)

Iteration U. Outcomes 1 and 3 stay open.

Route checkpoint. Another prefix length does not discharge outcome 3.
Feeding `λ_min ≥ 1 / trace` back into the inverse-trace step multiplies
by a factor that unrolls exponentially in `k`. When `k = 3`, the
three-column prefix is the whole CPQR set. Success is that
identification: `milestoneE_equal_energy_cpqr_k3`. Exit if `cpqrSet` is
not `cpqrIterate 3` at `k = 3`, or if `5n - 12 + 6/n` disagrees with the
phase-T expression.

Target in `StructuredColumnSelection/EqualEnergyPivot.lean`, re-exported
as `milestoneE_equal_energy_cpqr_k3`: if the rows are orthogonal, every
column energy is equal, `k = 3`, and `0 < n`, then the CPQR set has three
columns, its inverse trace is at most `5n - 12 + 6/n`, and
`‖x‖² ≤ (5n - 12 + 6/n) ‖A_J x‖²`.

Independent check: `tests/test_equal_energy_k3.py` uses exact arithmetic
on the `3×3` identity. The closed form equals the phase-T expression and
equals `5`, and the inverse trace is `3`. It does not call the repository
CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound for equal-energy matrices of every
`k`, no closure of outcome 1 or outcome 3, and no claim that Problem 4.1
is solved. Equal energy is stricter than the weakest SPEC §10 class. The
outcome-2 family has `k = m² ≥ 4`, so this three-row statement does not
apply to it. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#34](https://github.com/tripp-smith/structured-column-selection/pull/34).

## Phase V leverage-ratio pivot split (2026-10-29, contract)

Iteration V. Outcomes 1 and 3 stay open.

Route checkpoint. Another equal-energy prefix length does not discharge
outcome 3, and the `λ_min ≥ 1 / trace` recurrence unrolls exponentially
in `k`. Phase R's second-pivot agreement uses equal column energy, which
is leverage ratio `1`. The question for this phase is whether a leverage
ratio strictly above `1` keeps that agreement. Success is a certified
orthogonal-row witness whose column-energy ratio is `32/13` and whose
CPQR set differs from the increment set:
`milestoneE_leverage_ratio_pivot_split`. Exit if the energies leave
`[13/50, 16/25]` or the two selected sets agree.

Target in `StructuredColumnSelection/LeverageRatioSplit.lean`, re-exported
as `milestoneE_leverage_ratio_pivot_split`: there is an orthogonal-row
`2×5` matrix whose column energies lie in `[13/50, 16/25]`, attain both
endpoints, hence have ratio `(16/25) / (13/50) = 32/13`, and on which
`incrementSet ≠ cpqrSet`.

Independent check: `tests/test_leverage_ratio_split.py` recomputes the
row dots, the five energies, the common residual `1/4`, and the four
increment ratios from the integer columns. It does not call the
repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound on the leverage-ratio class, no
claim that every matrix of ratio `32/13` splits, and no closure of
outcome 1 or outcome 3. Equal energy remains the case in which the
second pivots agree. Problem 4.1 is not solved. `MinDimLe`, `k = 1`,
and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#35](https://github.com/tripp-smith/structured-column-selection/pull/35).

## Phase W orthogonal equal-energy block (2026-10-29, contract)

Iteration W. Outcomes 1 and 3 stay open.

Route checkpoint. Transferring `milestoneE_increment_set_bound` to CPQR
would need the CPQR column's increment ratio to stay at most
`((n - t) + trace(G⁻¹) - t) / (k - t)`. The estimate
`‖G⁻¹ w‖² ≤ q / λ_min`, using `λ_min ≥ (k - 1) / (2 (n - 1))` and
residual at least `(k - 2) / (n - 2)`, does not prove that. At `k = 3`,
`n = 6`, and `λ_min = 2/5`, which is feasible for the second-residual
constraint, the left side is `13/8` and the allowance is `37/24`, and
`13/8 > 37/24`. The two sides meet when the two-column Gram is a scalar
multiple of the identity. That overshoot is an obstruction to this
estimate. It is not a theorem that the true CPQR ratio exceeds the
average.

Target in `StructuredColumnSelection/OrthogonalBlockPivot.lean`,
re-exported as `milestoneE_equal_energy_orthogonal_block_same_pivot`:
if the rows are orthogonal, every column has the same energy, and the
selected columns in `J` are pairwise orthogonal, then
`cpqrPivot A J = incrementPivot A J`. The Gram is `(k / n)` times the
identity, so the increment ratio equals `(2e - r) / (e r)` and is
strictly decreasing in the residual. A one-column block is the
agreement half of phase R. Blocks of size at least `2` are the new case.

Independent check: `tests/test_orthogonal_block_pivot.py` checks the
`3×3` identity ratio `(2e - r) / (e r)` and the exact comparison
`13/8 > 37/24`. The comparison is a failed estimate, not a certificate
that CPQR exceeds the increment average. The test does not call the
repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound on equal-energy matrices or on the
leverage-ratio class, and no closure of outcome 1 or outcome 3. The
orthogonal-block hypothesis is a condition on the selected set `J`. It
is not the SPEC §10 class `ColumnIncoherent A 0`, which asks every pair
of columns to be orthogonal and is already phase P. This theorem does
not say every equal-energy CPQR prefix is orthogonal. Problem 4.1 is
not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#36](https://github.com/tripp-smith/structured-column-selection/pull/36).

## Phase X equal-energy block split (2026-10-29, contract)

Iteration X. Outcomes 1 and 3 stay open.

Route checkpoint. Phase W shows that an orthogonal equal-energy block
makes the next pivots agree. Dropping orthogonality is a different
question from extending the CPQR prefix. A search of the integer tight
frames with column squared length `25` and `50` found no split along a
CPQR path. One ordering of a squared-length `17` frame numerically
separates the third pivot; that search is not a certificate. The
length-`50` frames do separate the two rules on a non-orthogonal
block, and that separation is the theorem below. Success is a
certified equal-energy witness of that block separation:
`milestoneE_equal_energy_block_pivot_split`. Exit if columns `0` and `1`
are orthogonal, or if the two pivots on `{0, 1}` agree.

Target in `StructuredColumnSelection/EqualEnergyBlockSplit.lean`,
re-exported as `milestoneE_equal_energy_block_pivot_split`: the columns

```
(-7, -4, -4, -3, -3, -1),
(-1, -3, -3,  4,  4,  7),
( 0, -5,  5, -5,  5,  0)
```

divided by `10` have orthogonal rows and column energy `1/2`. Columns
`0` and `1` have inner product `31/100`. After that block, CPQR takes
column `5` and the increment pivot takes column `3`. Column `5` is
orthogonal to column `0`.

Independent check: `tests/test_equal_energy_block_split.py` recomputes
the integer row Gram, the common squared length `50`, the block inner
product `31`, the orthogonality `dot(c0, c5) = 0`, and the `2×2` inverse
residuals and ratios. It does not call the repository CPQR code. It is
not the theorem.

Non-claims: no polynomial CPQR bound on equal-energy matrices, and no
closure of outcome 1 or outcome 3. This witness does not say
`cpqrSet ≠ incrementSet`. The disagreeing block is not pairwise
orthogonal, so it is outside phase W, and column `5` being orthogonal
to column `0` means `{0, 1}` is not the two-column CPQR prefix. Problem
4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#43](https://github.com/tripp-smith/structured-column-selection/pull/43).

## Phase AE scaled leading block (2026-10-30, contract)

Iteration AE. Outcomes 1 and 3 stay open.

Route checkpoint. The triple design of phase AD has column energy
`1 / (4 (k-1)(k-2))`, and the design-frame pivot theorem of phase AB
needs filler energy below `1 / (32 k³)`. The gap closes by scaling the
leading block: with `R = s R₀` for `R₀ = wideTriangular m` and a
constant `s`, every leading residual is at least `s² α² / 4 = s² / (16 k²)`
while the total filler energy stays below `k`. Two facts make the scale
affordable. First, the entry bound `|R₀ i j| ≤ α` used so far gives
`‖R₀‖_F² ≤ 1/4`; the row structure (one diagonal `≤ α`, at most `k`
off-diagonal entries `≤ c α`, and `k c² < 1/4`) gives
`‖R₀‖_F² ≤ 5 / (16 k)`, so `‖3 R₀‖_F² ≤ 45 / (16 k) ≤ 1` for `k ≥ 3` and
the symmetric completion of phase AC applies. Second, that completion
contracts, `‖C w‖² ≤ ‖w‖²`, so the filler energy is at most the design
column energy, with no factor `k`. With `s = 3` the requirement
`1 / (4 (k-1)(k-2)) ≤ 9 / (16 k²)` holds for `k ≥ 5`, so for every
`m ≥ 3` the frame `[3 R₀ | C W]` with the triple design `W` has
orthogonal rows, CPQR set equal to the leading prefix, and inverse
growth at least `((2m/3)(4/3)^(m-1))² / 9`.

Targets in `StructuredColumnSelection/ScaledDesignFrame.lean`:
`wideTriangular_frob_le_sharp` (`‖R₀‖_F² ≤ 5 / (16 k)`),
`wide_scaled_design_pivots` (parametric in `s > 0`, the completion
`C` with `(s R₀)(s R₀)ᵀ + C Cᵀ = 1` and `‖C w‖² ≤ ‖w‖²`, and a tight
design with column energy `≤ s² / (16 k²)`: orthogonal rows and CPQR
set equal to the prefix), `wide_scaled_design_adverse` (the same with a
witness `x`, `‖A_J x‖² = 1`, `‖x‖² ≥ G² / s²`), a row-reindexing lemma
for designs, and the instantiation `scaled_triple_frame`: for every
`m ≥ 3` there are `A`, `C`, `W`, `x` with `A Aᵀ = 1`, leading block
`3 R₀`, filler block `C W`, `Cᵀ = C`, `(3 R₀)(3 R₀)ᵀ + C Cᵀ = 1`,
`‖3 R₀‖_F² ≤ 45 / (16 k)`, `W Wᵀ = 1`, every design column of energy
`1 / (4 (k-1)(k-2))`, design coherence at most `13/14`, CPQR set equal
to the prefix, `‖A_J x‖² = 1`, and `G² / 9 ≤ ‖x‖²`. Re-exported as
`milestoneE_scaled_triple_frame`.

Independent check: `tests/test_scaled_block.py` builds `R₀` for
`m = 2, 3, 4` in exact rationals, checks `‖R₀‖_F² ≤ 5 / (16 k)`, checks
`1 / (4 (k-1)(k-2)) ≤ 9 / (16 k²)` for `5 ≤ k ≤ 200`, and checks on the
`m = 3` instance with a floating completion `C = (I - R Rᵀ)^{1/2}` that
every filler energy is below every leading residual threshold and that
the greedy pivots are the leading prefix. It does not call the
repository CPQR code. It is not the theorem.

Non-claims: no coherence bound on the frame `[3 R₀ | C W]` is proved in
this phase (the design coherence `13/14` is a statement about `W`, not
about `C W` or about the leading columns); no polynomial CPQR bound; no
closure of outcome 1 or outcome 3. Problem 4.1 is not solved.
`MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#44](https://github.com/tripp-smith/structured-column-selection/pull/44).

## Phase AF frame coherence, filler pairs (2026-10-30, contract)

Iteration AF. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AE builds the orthogonal-row frame `[3 R₀ | C W]`
and records the completion identities of `C` and the `13/14` coherence of
the design `W`. Those facts do not yet bound inner products of columns of
the frame. Two filler columns are `C w_a` and `C w_b`. The inner-product
identity writes `⟨C w_a, C w_b⟩ - ⟨w_a, w_b⟩` as `-⟨Rᵀ w_a, Rᵀ w_b⟩`, and
Cauchy–Schwarz with `‖Rᵀ w‖² ≤ ε ‖w‖²` bounds that error by
`ε √(‖w_a‖² ‖w_b‖²)`. The energy lower bound
`(1 - ε) ‖w‖² ≤ ‖C w‖²` turns the design ratio `13/14` into the normalized
filler ratio `(13/14 + ε)/(1 - ε)`. A leading column `r_j` meets a filler
through `⟨r_j, C w⟩ = ⟨r_j, w⟩ + ⟨r_j, (C - I) w⟩`. The design column is
supported on three coordinates with weights `1, 2, 3`, and the triangular
column `r_j = 3 R₀ e_j` is `3 diag_j` on the diagonal and at most
`3 c α` off it, with `c α ≤ diag_j / m`. At most one support coordinate is
the diagonal, so `⟨r_j, w⟩` is at most `3(1 + 1/m)/√14` times the product
of the norms, and the normalized leading–filler ratio is at most
`(3(1 + 1/m)/√14 + ε)/√(1 - ε)`, where `ε = 45/(16 k)`. The row reindexing
of the design moves the three support coordinates by `e.symm` and does not
change the weights. Leading–leading pairs use a different inner-product
formula and are not bounded in this phase. Exit if `ε ≥ 1` (it is not:
`k ≥ 9`) or if the three support coordinates fail to stay distinct after
reindexing.

Targets in `StructuredColumnSelection/FrameCoherence.lean`:
`completion_inner_perturb`, `filler_filler_ratio`, `leading_filler_ratio`,
`triple_column_inner_le` (and its transfers to `tripleDesignFin` and to the
row-reindexed submatrix), the leading-column ratio
`scaledBlock_design_inner_le`, and the instantiation
`scaled_triple_frame_filler_coherence`: for every `m ≥ 3`, the data of
`scaled_triple_frame` together with filler–filler normalized coherence at
most `(13/14 + ε)/(1 - ε)` and leading–filler normalized coherence at most
`(3(1 + 1/m)/√14 + ε)/√(1 - ε)`, with `ε = 45 / (16 k)`. Re-exported as
`milestoneE_scaled_triple_frame_filler_coherence`.

Independent check: `tests/test_frame_coherence.py` builds the `m = 3` frame
as in `tests/test_scaled_block.py`, with `ε = 9 ‖R₀‖_F²` computed in exact
rationals, and checks every filler–filler ratio against
`(13/14 + ε)/(1 - ε)` and every leading–filler ratio against
`(3(1 + 1/3)/√14 + ε)/√(1 - ε)`. It also checks that those ratios are
strictly below `1` on this instance. The displayed bounds may exceed `1`
for `m = 3`; the test checks the formulas. It does not call the repository
CPQR code. It is not the theorem.

Non-claims: leading–leading pairs are not bounded; no coherence bound on
the whole frame is claimed; the proved filler–filler and leading–filler
expressions are not claimed to be strictly less than `1` for every
`m ≥ 3`; no polynomial CPQR bound; no closure of outcome 1 or outcome 3.
Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#45](https://github.com/tripp-smith/structured-column-selection/pull/45).

## Phase AG leading–leading coherence (2026-10-30, contract)

Iteration AG. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AF bounds filler–filler pairs and each leading
column against each filler of the scaled triple-design frame. Leading
columns of `wideTriangular m` were left open. Column `t` is supported on
rows `l ≤ t`: the diagonal entry is `diag_t = wideDiagNat m t`, and the
entry in row `l < t` is `-wideC m * diag_l`. For `(i : ℕ) < (j : ℕ)`,

```
S_i = wideC m ^ 2 * ∑_{l < i} (wideDiagNat m l) ^ 2
⟨col i, col j⟩ = -wideC m * diag_i ^ 2 + S_i
vecEnergy (col i) = diag_i ^ 2 + S_i
vecEnergy (col j) = diag_j ^ 2 + S_j
```

with `S_j ≥ S_i`. `wideDiag_half_lower` gives `wideAlpha m / 2 < diag` on
indices below `k = wideDim m`, so `diag ^ 2 > wideAlpha m ^ 2 / 4`, and
`wideDiag_le_alpha` gives `diag ≤ wideAlpha m`. `wide_kc_sq_le` gives
`k * wideC m ^ 2 ≤ 1/4`, hence `S_i ≤ wideAlpha m ^ 2 / 4`. The absolute
inner product is at most `wideC m * wideAlpha m ^ 2 + S_i`, while the
product of the norms is strictly above `wideAlpha m ^ 2 / 4 + S_i`.
Writing `u = S_i / wideAlpha m ^ 2 ∈ [0, 1/4]`, the ratio is strictly
below `(wideC m + u) / (1/4 + u)`. For `0 ≤ wideC m ≤ 1/4` this increases
in `u`, and the value at `u = 1/4` is `2 * wideC m + 1/2`. Since
`wideC m = 2m / (4m^2 + 1) ≤ 1/(2m)`, one has
`2 * wideC m + 1/2 ≤ 1/2 + 1/m`. The diagonal lower bound is strict, so
the non-strict comparison holds. Symmetry covers `j < i`. The factor `3`
on `scaledBlock m = (3 : ℝ) • wideTriangular m` multiplies inner products
by `9` and energies by `9`, and the ratio is unchanged. Exit if
`wideC m > 1/4` for some `m ≥ 2` (it is not: `wideC m ≤ 1/(2m) ≤ 1/4`)
or if a leading diagonal fails `wideAlpha m / 2 < diag`.

Target in `StructuredColumnSelection/LeadingCoherence.lean`, re-exported
as `milestoneE_scaled_block_leading_coherence`: for every `m ≥ 2` and all
`i ≠ j` in `Fin (wideDim m)`,

`|∑ row, scaledBlock m row i * scaledBlock m row j| ≤ (1/2 + 1/(m : ℝ)) * Real.sqrt (vecEnergy (fun row => scaledBlock m row i)) * Real.sqrt (vecEnergy (fun row => scaledBlock m row j))`.

Independent check: `tests/test_leading_coherence.py` builds
`wideTriangular m` in exact rationals for `m = 2, 3, 4` and checks every
pair `i < j` by comparing squares,
`inner^2 * 1 ≤ (1/2 + 1/m)^2 * energy_i * energy_j`, and the same
comparison for `scaledBlock = 3 * wideTriangular m`. It does not call the
repository CPQR code. It is not the theorem.

Non-claims: this does not bound filler pairs; a leading–leading ratio
`≤ 1/2 + 1/m` is not a coherence bound on the whole frame; no polynomial
CPQR bound; no closure of outcome 1 or outcome 3. Problem 4.1 is not
solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#46](https://github.com/tripp-smith/structured-column-selection/pull/46).

## Phase AH bounded coherence is not polynomial (2026-10-30, contract)

Iteration AH. Outcomes 1 and 3 stay open.

Route checkpoint. Phases AF and AG bound filler–filler, leading–filler, and
leading–leading pairs of the scaled triple-design frame, but they do not
put the whole frame under one normalized-coherence cap, and they do not
compare that cap with the polynomial scale. For `m ≥ 20`, `k = m² ≥ 400`
and `ε = 45/(16 k) ≤ 45/6400 < 1`. The filler ratio
`(13/14 + ε)/(1 - ε)` increases in `ε`, so its worst value on this range is

```
(13/14 + 45/6400) / (1 - 45/6400) = 83830/88970 < 19/20,
```

because `83830 * 20 = 1676600 < 1690430 = 19 * 88970`. Leading pairs are at
most `1/2 + 1/m ≤ 1/2 + 1/20 = 11/20 ≤ 19/20`. Leading–filler pairs are at
most `(3(1 + 1/m)/√14 + ε)/√(1 - ε)`. Since `(37/10)² = 1369/100 < 14`,
one has `√14 > 37/10`, hence `1/√14 < 10/37` and
`3(1 + 1/20)/√14 < 63/74`. The squared comparison

```
(63/74 + 45/6400)² < (19/20)² * (1 - 45/6400)
```

then puts the mixed ratio strictly below `19/20`. Exit if `83830/88970`
fails to sit under `19/20`, or if the squared comparison fails: either
would mean the constant has to move.

The same `m` is large enough for the polynomial. Call
`exists_scale_beats_polynomial d (0 < 9 * C) 20`. The frame has
`n = k + 4 k (k - 1) (k - 2)` columns, image energy `1`, and inverse
energy at least `wideGrowthLower m ^ 2 / 9`. For `k ≥ 1`,
`4 k (k - 1) (k - 2) ≤ 4 k³ ≤ 32 k⁴`, so
`n + k + 1 ≤ wideWidth m + wideDim m + 1 = 2k + 32 k⁴ + 1`. Monotonicity
of `t ↦ t^{2d}` on `[1, ∞)` transfers the strict inequality
`9 C (wideWidth + wideDim + 1)^{2d} < wideGrowthLower m ^ 2` into
`C (n + k + 1)^{2d} < wideGrowthLower m ^ 2 / 9 ≤ ‖x‖²`.

Target in `StructuredColumnSelection/BoundedCoherence.lean`, re-exported
as `milestoneE_bounded_coherence_no_polynomial`: for every `d : ℕ` and
every `C : ℝ` with `0 < C`,

```
∃ k n, ∃ A : Matrix (Fin k) (Fin n) ℝ, ∃ x : Fin (cpqrSet A).card → ℝ,
  OrthogonalRows A ∧
  (∀ j, 0 < residualSq A ∅ j) ∧
  (∀ j1 j2, j1 ≠ j2 →
    |colInner A j1 j2| ≤ (19/20) *
      (Real.sqrt (residualSq A ∅ j1) * Real.sqrt (residualSq A ∅ j2))) ∧
  C * ((n + k + 1 : ℕ) : ℝ) ^ (2 * d) *
    vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) < vecEnergy x
```

Independent check: `tests/test_bounded_coherence.py` checks
`83830/88970 < 19/20`, `1/2 + 1/20 ≤ 19/20`,
`(63/74 + 45/6400)² < (19/20)² * (6355/6400)`, and `(37/10)² < 14`, in
exact `fractions.Fraction` arithmetic. It does not call the repository
CPQR code. It is not the theorem.

Non-claims: this shows that normalized coherence `≤ 19/20` does not
restore a polynomial CPQR bound. Any `ρ ≥ 19/20` is too weak for the
same reason, because coherence `≤ 19/20` implies coherence `≤ ρ`. A
smaller `ρ` is not ruled out. This does not close outcome 1 or outcome 3.
It is not a polynomial bound for every orthogonal-row matrix. Problem 4.1
is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#47](https://github.com/tripp-smith/structured-column-selection/pull/47).

Phase PR and verification receipt:
[#37](https://github.com/tripp-smith/structured-column-selection/pull/37).

## Phase Y equal-energy third pivot (2026-10-29, contract)

Iteration Y. Outcomes 1 and 3 stay open.

Route checkpoint. Phase X separates the two rules on a non-orthogonal
equal-energy block that CPQR does not choose. The open question is
whether they still agree along the CPQR path. Success is a certified
split of that path:
`milestoneE_equal_energy_third_pivot_split`. Exit if the third pivots
on `{0, 2}` agree, or if the second pivots on `{0}` differ.

Target in `StructuredColumnSelection/EqualEnergyThirdPivot.lean`,
re-exported as `milestoneE_equal_energy_third_pivot_split`: the columns

```
(-3, -4, -2, -2, -1,  0),
(-2, -1,  2,  3,  0, -4),
(-2,  0,  3, -2,  4,  1)
```

divided by `√34` have orthogonal rows and column energy `1/2`. Both
rules take column `0` and then column `2`. After `{0, 2}`, CPQR takes
column `3` and the increment pivot takes column `5`. The sets are
`{0, 2, 3}` and `{0, 2, 5}`. Columns `0` and `2` have inner product
`-2/17`.

Independent check: `tests/test_equal_energy_third_pivot.py` recomputes
the integer row Gram `34 I`, the common squared length `17`, the second
pivot tie at residual `273/578`, and the `2×2` inverse residuals and
ratios after `{0, 2}`. It does not call the repository CPQR code. It is
not the theorem.

Non-claims: no polynomial CPQR bound on equal-energy matrices, and no
closure of outcome 1 or outcome 3. Equal energy is stricter than the
weakest SPEC §10 class. The bound is for this `k = 3` frame; the
outcome-2 family has `k = m² ≥ 4`. Phase W still makes an orthogonal
block agree, and phase X's `{0, 1}` split is a different block. The
integer search that found this ordering is not the theorem. Problem
4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#38](https://github.com/tripp-smith/structured-column-selection/pull/38).

## Phase Z absolute incoherence escape (2026-10-29, contract)

Iteration Z. Outcomes 1 and 3 stay open.

Route checkpoint. Phase Y separates the CPQR path from the increment
pivot on one equal-energy frame. That does not put the outcome-2 family
inside a leverage-ratio class: the family leaves every fixed ratio.
Absolute inner-product incoherence goes the other way. Every column
energy of an outcome-2 frame is at most `1 / (2k)`, so Cauchy–Schwarz
puts the frame in `ColumnIncoherent A ρ` once `k` is large. Success is
`milestoneE_incoherent_no_joint_polynomial`: for every `ρ > 0`, every
degree, and every positive coefficient, some frame in that class beats
`C (n + k + 1)^{2d}`. Exit if some positive `ρ` excludes every outcome-2
frame.

Target in `StructuredColumnSelection/WideIncoherentEscape.lean`,
re-exported as `milestoneE_incoherent_no_joint_polynomial`.

Independent check: `tests/test_wide_incoherent_escape.py` recomputes the
`m = 2` triangular entries from `wideAlpha`, `wideEps`, and `wideC`, and
checks column energies and off-diagonal inner products against
`1 / (2k)`. It also checks the filler cap `k / (32 k³)`. It does not
call the repository CPQR code. It is not the theorem.

Non-claims: no polynomial CPQR bound, and no closure of outcome 1 or
outcome 3. `ColumnIncoherent` bounds absolute inner products. It is not
the normalized coherence ratio in SPEC §10. Phase P still bounds the
case `ρ = 0`, and phase Q still places the outcome-2 frame outside that
case. Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay
outside outcome 3.

Phase PR and verification receipt:
[#39](https://github.com/tripp-smith/structured-column-selection/pull/39).

## Phase AA normalized coherence (2026-10-29, contract)

Iteration AA. Outcomes 1 and 3 stay open.

Route checkpoint. Phase Z places the outcome-2 frame inside absolute
inner-product incoherence `ColumnIncoherent A ρ` for every `ρ > 0`.
The remaining named SPEC §10 candidate is the normalized ratio
`|⟨a_i, a_j⟩| / (|a_i| |a_j|)`. The padded frame repeats each completion
column at least twice. The triangular block has Frobenius energy at most
`1` and `k ≥ 2`, so the completion has positive Frobenius energy and some
repeated column is nonzero. Two copies are identical, so the ratio of
that pair is `1`. Success is `milestoneE_normalized_coherence_one`. Exit
if every repeated completion column has energy `0`.

Target in `StructuredColumnSelection/NormalizedCoherence.lean`,
re-exported as `milestoneE_normalized_coherence_one`.

Independent check: `tests/test_normalized_coherence.py` checks that two
copies of one nonzero rational column have ratio `1`, and that the
`m = 2` triangular Frobenius energy is at most `1/4` while `k` exceeds
that energy and `32 k³ ≥ 2`. It does not call the repository CPQR code.
It is not the theorem.

Non-claims: no polynomial CPQR bound on matrices whose normalized
coherence is strictly below `1`, and no closure of outcome 1 or
outcome 3. The proved pair has ratio `1`. A bound at ratio `1` is the
Cauchy–Schwarz ceiling for nonzero columns. `ColumnIncoherent` still
bounds absolute inner products, and phase Z still places the family
inside every `ρ > 0`. Phase P still bounds the case `ρ = 0`, and phase Q
still places the outcome-2 frame outside that case. Problem 4.1 is not
solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#40](https://github.com/tripp-smith/structured-column-selection/pull/40).

## Phase AB design-padded adverse family (2026-10-30, contract)

Iteration AB. Outcomes 1 and 3 stay open.

Route checkpoint. Of the SPEC §10 candidates, the outcome-2 family
leaves every leverage ratio (phase G), enters every absolute
incoherence `ρ > 0` (phase Z), and has normalized coherence exactly `1`
(phase AA) because the filler block repeats columns. The open question
for the normalized ratio is whether some orthogonal-row frame with every
ratio at most a fixed `ρ < 1` still beats every polynomial. The repeated
filler is the only reason the current frame has ratio `1`. This phase
replaces the repeat `(1/√t)[I ⋯ I]` by an arbitrary tight design
`W` with `W Wᵀ = 1`: the filler block is `C W` for any completion
`R Rᵀ + C Cᵀ = 1`. The CPQR prefix only needs every filler energy below
the smallest squared diagonal, and `‖C w‖² ≤ ‖C‖_F² ‖w‖² ≤ k ‖w‖²`
gives that from a per-column energy cap on `W`. Success is
`milestoneE_design_adverse_family`: for every `m ≥ 2`, every completion
`C`, and every design `W` with `W Wᵀ = 1` and column energy at most
`1 / wideRepeats m`, the design frame has orthogonal rows, leading
block `wideTriangular m`, filler block `C W`, CPQR set equal to the
leading prefix, image energy `1`, and inverse energy at least
`wideGrowthLower m ^ 2`. Downstream consumer: a later phase chooses `W`
and `C` to bound the normalized coherence of every column pair below
`1`. Exit if the prefix argument needs the repeated structure.

Target in `StructuredColumnSelection/DesignFrame.lean`, re-exported as
`milestoneE_design_adverse_family`. The repeated frame is the design
`W = (1/√t)[I ⋯ I]`; `milestoneE_wide_adverse_family` is unchanged.

Independent check: `tests/test_design_frame.py` builds a rational `2×2`
leading block, a rational completion, and a design made of four
rational orthonormal bases scaled by `1/2`. It checks `W Wᵀ = I`,
`A Aᵀ = I` for `[R | C W]`, the filler energy cap `k ‖w‖²`, and that
no two filler columns are parallel. It does not call the repository
CPQR code. It is not the theorem.

Non-claims: no coherence bound is proved in this phase; the design is
arbitrary, and the frame with the repeated design still has normalized
coherence `1`. No polynomial CPQR bound, and no closure of outcome 1 or
outcome 3. Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2`
stay outside outcome 3.

Phase PR and verification receipt:
[#41](https://github.com/tripp-smith/structured-column-selection/pull/41).

## Phase AC symmetric completion (2026-10-30, contract)

Iteration AC. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AB lets the filler block be `C W` for any
completion `C` and any tight design `W`. The normalized coherence of two
filler columns is `|⟨C w_a, C w_b⟩| / (‖C w_a‖ ‖C w_b‖)`, and of a
leading column with a filler is `|⟨r_j, C w_a⟩| / (‖r_j‖ ‖C w_a‖)`.
Both need `C` to act almost like the identity. The existential
completion of `exists_gram_completion` carries no such control. The
symmetric positive semidefinite square root `C = (1 - R Rᵀ)^{1/2}` does:
with `ε = ‖R‖_F²`, `⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`,
`(1 - ε) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and `‖(C - I) v‖² ≤ ε² ‖v‖²`. The last
bound uses `(C + I)(C - I) = -R Rᵀ` and `‖(C + I) u‖² ≥ ‖u‖²` for
`C ⪰ 0`; no spectral decomposition is needed. Success is
`milestoneE_symmetric_completion`. Downstream consumer: the normalized
coherence bounds of the design frame in a later phase. Exit if the
square root is not available as a symmetric matrix in the current
mathlib.

Target in `StructuredColumnSelection/SymmetricCompletion.lean`,
re-exported as `milestoneE_symmetric_completion`: for every `R` with
`‖R‖_F² ≤ 1` there is `C` with `Cᵀ = C`, `R Rᵀ + C Cᵀ = 1`, the inner
product identity, the energy sandwich, and the perturbation bound.

Independent check: `tests/test_symmetric_completion.py` checks the
three bounds on two rational pairs `(R, C)` with `Cᵀ = C` and
`C² = I - R Rᵀ`: a diagonal pair with `‖R‖_F² = 9/25`, and a rank-one
projection pair. It does not call the repository CPQR code. It is not
the theorem.

Non-claims: no coherence bound on any frame is proved in this phase; no
polynomial CPQR bound; no closure of outcome 1 or outcome 3. Problem 4.1
is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#42](https://github.com/tripp-smith/structured-column-selection/pull/42).

## Phase AD weighted triple design (2026-10-30, contract)

Iteration AD. Outcomes 1 and 3 stay open.

Route checkpoint. Phases AB and AC reduce a bounded-coherence adverse
frame to one missing ingredient: an explicit tight design
`W Wᵀ = 1` in `ℝ^k` with many columns, every column of small energy,
and every pair of distinct columns at normalized inner product bounded
away from `1`. Counting fixes the size: the filler block carries total
energy `k - ‖R‖_F²`, and every filler must stay below the smallest
leading residual, so the number of pairwise non-parallel filler
directions must grow at least like `k²` (after rescaling the leading
block) and like `k³` without rescaling. Repeating columns, as in the
outcome-2 frame, gives normalized coherence exactly `1`
(`milestoneE_normalized_coherence_one`), so repetition is not allowed.

The design used here is the weighted signed triple design. For
`k = n + 3`, index columns by `(p, q, r, σ, τ)` with `p : Fin (n+3)`,
`q : Fin (n+2)`, `r : Fin (n+1)`, `σ τ : Bool`. Put
`q' = p.succAbove q` and `r' = p.succAbove (q.succAbove r)`, so
`p, q', r'` are three distinct coordinates, and set

```
v = e_p + 2σ e_{q'} + 3τ e_{r'},      W = v / √(56 (n+2)(n+1)).
```

Sign sums kill every cross term, so `W Wᵀ = 1`. Every column has energy
`14 / (56 (n+2)(n+1)) = 1 / (4 (n+2)(n+1))`. The integer inner product of
two distinct columns has absolute value at most `13` (it is an integer,
Cauchy–Schwarz gives at most `14`, and `±14` forces `v_a = ±v_b`, which
the coefficient `+1` at `p` rules out), so the normalized coherence of
two distinct columns is at most `13/14`. The constant `13/14` is
attained (swap the weights `1` and `2`); it is not claimed to be
optimal.

Target in `StructuredColumnSelection/TripleDesign.lean`, re-exported
as `milestoneE_triple_design`: for every `n`, a matrix
`W : Matrix (Fin (n+3)) (Fin (4 (n+3)(n+2)(n+1))) ℝ` with `W Wᵀ = 1`,
every column energy equal to `1 / (4 (n+2)(n+1))`, and
`|⟨w_a, w_b⟩| ≤ (13/14) √(‖w_a‖²) √(‖w_b‖²)` for all `a ≠ b`.

Independent check: `tests/test_triple_design.py` builds the design for
`k = 3, 4, 5, 6` in exact rationals (the normalization is kept as the
square `56 (n+2)(n+1)` so no square roots are needed), checks
`W Wᵀ = I`, the column energy, pairwise non-parallelism, and the
integer inner-product bound `13`. It does not call the repository CPQR
code. It is not the theorem.

Non-claims: no adverse frame is built in this phase; the design column
energy `1 / (4 (n+2)(n+1))` is above the `1 / wideRepeats` cap of
`wide_design_pivots`, so `milestoneE_design_adverse_family` is not
instantiated here; no coherence bound on any orthogonal-row frame; no
polynomial CPQR bound; no closure of outcome 1 or outcome 3. Problem
4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

## Phase AI joint leverage-coherence census (2026-10-30, contract)

Iteration AI. Outcomes 1 and 3 stay open. This phase is Python only.
There is no new public Lean declaration, and `Theorems.lean` is unchanged.

Route checkpoint. `milestoneE_bounded_coherence_no_polynomial` shows that
normalized coherence at most `19/20` does not restore a polynomial CPQR
bound. The frame in that theorem is the scaled triple-design frame. Its
column leverages are wildly unbalanced, so the theorem does not exclude
the joint class in this census. The joint class is matrices with
orthogonal rows (`A Aᵀ = I`, float tolerance) such that the leverage
ratio `max_j ℓ_j / min_j ℓ_j` is at most `τ` and the normalized coherence

```
max_{i≠j} |⟨col i, col j⟩| / (‖col i‖ ‖col j‖)
```

is at most `ρ`, where `ℓ_j = ‖column j‖²`. A frame with measured leverage
ratio `L` and normalized coherence `c` belongs to every cell with
`τ ≥ L` and `ρ ≥ c`. The census asks what `r_CPQR` does on a finite
sample of that class. It does not prove the class is safe, and it does
not prove the class grows.

`r_CPQR` is `‖A_J⁻¹‖₂ / √(k(n-k+1))`, taken from `evaluate`. The
named-polynomial comparison is `named_poly_scale`. `normalized_coherence`
is a separate function. `max_abs_col_inner` stays the absolute
off-diagonal column inner product.

Grid: `τ ∈ {2, 4, 8}`, `ρ ∈ {0.5, 0.7, 0.9}`, `k = 2..8`, `n ≤ 16`.
Hadamard, Fourier, leverage-skew, near-duplicate, and Kahan-like frames
are built for every such `k` and every `n` in
`{k+1, min(2k, 16)}` together with the powers of two satisfying
`k < n ≤ 16`. ETF, clustered, and block frames use the constructors
already in `structselect/census.py` whose shapes lie in this range.
The Haar sample uses seed 1 and 20 draws for each `(k, n)` with
`n ∈ {k+1, min(2k, 16)}`. A tried frame is accepted when every leverage
is finite and positive, `aat_err < 1e-8`, `r_CPQR` is finite, CPQR
returns `k` columns, and at least one cell contains the frame. Zero
columns are rejected. The scaled triple-design frame is not rerun: its
row count is `m² ≥ 9`, outside this census.

Artifact: `experiments/census_joint_seed1.json`, written through
`require_clean_worktree`. `closes_milestone_e` is false. Evidence is
numeric. A recorded ratio is not a theorem. An empty cell stays empty.

Non-claims: this does not close §8 or §10; outcome 3 stays open; no
polynomial CPQR bound; Problem 4.1 is not solved. `MinDimLe`, `k = 1`,
and `k = 2` stay outside outcome 3. The search is finite.

Reading of `experiments/census_joint_seed1.json` (seed 1, revision
`5d41fd9b7a41ddf87e1a17248861724fd621a2a3`). 428 frames were tried and
228 were accepted. All nine cells are nonempty. The largest recorded
`r_CPQR` is `0.866025403784439`, on the `2×3` simplex ETF, in every
cell with `ρ ≥ 0.7`. The `ρ = 0.5` maxima are `0.8164965809277263`,
on the `3×4` simplex ETF. Measured coherence of the `2×3` equiangular
frames sits one unit in the last place above `1/2`, so those frames
are outside the `ρ = 0.5` cells. Inside every cell, the per-`k`
maximum does not increase with `k`. No accepted frame has `r_CPQR > 1`,
and none meets `named_poly_scale`. Hypothesis, not a theorem: no growth
was observed on this finite search, so a later phase may try a positive
theorem on the joint class. The sample does not prove the class is safe
and does not prove it grows.

Phase PR and verification receipt:
[#48](https://github.com/tripp-smith/structured-column-selection/pull/48).

## Phase AJ joint pair Gram (2026-10-30, contract)

Iteration AJ. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AI's seed-1 census motivated a positive
two-column question on the joint leverage-ratio and coherence class.
That census is numeric. It is not a hypothesis of the theorem below,
and it is not an input to the proof.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_pair_inv_trace`. For `A : Matrix (Fin k) (Fin n) ℝ`
with `OrthogonalRows A`, integers `2 ≤ k` and `1 ≤ n`, and reals
`1 ≤ τ` and `0 ≤ ρ < 1`, if

```
∀ i j, residualSq A ∅ i ≤ τ * residualSq A ∅ j
```

and

```
∀ i ≠ j, |colInner A i j| ≤ ρ * sqrt(residualSq A ∅ i) * sqrt(residualSq A ∅ j),
```

then for all `i ≠ j` the Gram `selectedColGram A {i, j}` is invertible and

```
((selectedColGram A {i, j})⁻¹).trace ≤
  2 * τ ^ 2 * n / (k * (1 - ρ ^ 2)).
```

The constant is that expression. It is not replaced by a looser one.
Column energies sum to `k`, so some energy is at least `k/n`, the
leverage hypothesis puts every energy at least `(k/n)/τ`, and the
coherence hypothesis makes the Gram determinant at least
`ℓ_i ℓ_j (1 - ρ^2)`. The inverse trace of the symmetric `2×2` is
`(ℓ_i + ℓ_j) / det`.

`cpqrIterate A 2` is not part of the statement. A bound on every pair
does not identify the CPQR pivots.

Independent check: `tests/test_joint_pair.py`, in `fractions.Fraction`.
The `2×2` identity has inverse trace `2`, equal to the formula at
`τ = 1`, `ρ = 0`, `k = 2`, `n = 2`. The parameters `ℓ_i = ℓ_j = 2/3`
and `c = ±1/3` have determinant `1/3` and inverse trace `4`, equal to
the formula at `τ = 1`, `ρ = 1/2`, `k = 2`, `n = 3`. The test does not
call the repository CPQR code. It is not the theorem.

Non-claims: this bounds every 2-column Gram under a leverage-ratio and
coherence hypothesis. It does not bound a `k`-set for `k > 2`. It does
not close outcome 3. It is not a polynomial CPQR bound for every
orthogonal-row matrix. The hypothesis is not equivalent to every
`k`-subset being well-conditioned. The census did not prove this.
Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#49](https://github.com/tripp-smith/structured-column-selection/pull/49).

## Phase AK joint CPQR prefix (2026-10-30, contract)

Iteration AK. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AJ bounds every 2-column Gram. That theorem does
not mention CPQR. This phase specializes the same bound to the CPQR
prefix of length 2.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_prefix_trace`. Same hypotheses as
`joint_pair_inv_trace`, plus `2 ≤ n`: `OrthogonalRows A`, `2 ≤ k`,
`2 ≤ n`, `1 ≤ τ`, `0 ≤ ρ < 1`, the leverage comparison
`residualSq A ∅ i ≤ τ * residualSq A ∅ j` for all `i, j`, and the
coherence bound on `colInner` for `i ≠ j`.

Conclude:

```text
∃ j0 j1 : Fin n, j0 ≠ j1 ∧
  cpqrIterate A 2 = {j0, j1} ∧
  (selectedColGram A (cpqrIterate A 2)).det ≠ 0 ∧
  ((selectedColGram A (cpqrIterate A 2))⁻¹).trace ≤
    (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2))
```

The constant is that expression. It is not replaced by a looser one.
`j0` is not identified with index 0. Ties are broken by `cpqrPivot`;
the statement only needs existence.

Proof shape. `milestoneE_leverage_sum` says the empty residuals sum to
`k > 0`, so some column has `0 < residualSq A ∅ j`. The filter in
`cpqrPivot` requires a strictly positive residual equal to the max, so
`cpqrPivot A ∅ = some j0` and `cpqrIterate A 1 = {j0}`. The singleton
Gram of `{j0}` has nonzero determinant because that energy is positive
(`selectedColGram_singleton_det_ne_zero`). For every `j ≠ j0`,
`residualSq_eq_schur` gives
`residualSq A {j0} j = ℓ_j - c² / ℓ_j0`, which equals
`det(selectedColGram A {j0, j}) / ℓ_j0`. `joint_pair_inv_trace` says
that determinant is nonzero, and the energy is positive, so the Schur
residual is positive. Every unused column therefore has positive
residual, `cpqrPivot A {j0} = some j1` with `j1 ≠ j0`, and
`cpqrIterate A 2 = {j0, j1}`. Apply `joint_pair_inv_trace` to that pair.

Independent check: `tests/test_joint_cpqr_prefix.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On the `2×2`
identity, CPQR returns both columns and the inverse trace of that Gram
is `2`, equal to the formula at `τ = 1`, `ρ = 0`, `k = 2`, `n = 2`.
The test is not the theorem.

Non-claims: this is the CPQR prefix of length 2 under the joint
leverage-ratio and coherence hypothesis. It does not bound later pivots.
A 2-column CPQR prefix is not a `k`-set for `k > 2`. It does not close
outcome 3. It is not a polynomial bound for every orthogonal-row matrix.
The census did not prove this. Problem 4.1 is not solved. `MinDimLe`,
`k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#50](https://github.com/tripp-smith/structured-column-selection/pull/50).

## Phase AL joint CPQR Rayleigh (2026-10-30, contract)

Iteration AL. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AK bounds the inverse trace of the length-2 CPQR
Gram by `B = 2 τ^2 n / (k (1 - ρ^2))`. This phase turns that trace bound
into a Rayleigh lower bound on the same prefix. The coefficient is `1/B`.
It is not replaced by a smaller one.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_prefix_rayleigh`. Same hypotheses as
`joint_cpqr_prefix_trace`. For every
`x : Fin (cpqrIterate A 2).card → ℝ`,

```text
((k : ℝ) * (1 - ρ ^ 2)) / ((2 : ℝ) * τ ^ 2 * (n : ℝ)) * vecEnergy x ≤
  vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x)
```

Proof shape. The prefix theorem gives `J = cpqrIterate A 2` of card 2,
invertible `G = selectedColGram A J`, and `(G⁻¹).trace ≤ B`.
`vecEnergy_selectedCols` is the Gram identity
`vecEnergy (selectedCols A J *ᵥ x) = x ⬝ᵥ (G *ᵥ x)`. For
`H = !![a, c; c, b]` with `0 < a`, `0 < b`, and `0 < a * b - c ^ 2`, the
numerator of `(a + b) (xᵀ H⁻¹ x) - ‖x‖²` is
`(b x₁ - c x₂)² + (a x₂ - c x₁)²`. Apply that to `H = G⁻¹`, transported
from `Fin J.card` to `Fin 2` by `finCongr` because `J.card = 2`. The
diagonal energies of the Gram and the positive determinant from
`joint_pair_inv_trace` give `0 < a`, `0 < b`, and `0 < det`. The proof
does not unfold `cpqrPivot`. Then
`‖x‖² ≤ (G⁻¹).trace · ‖A_J x‖² ≤ B · ‖A_J x‖²`.

On the `2×2` identity the coefficient is `1/2` and the Rayleigh quotient
is `1`, because `λ_max ≤ trace`. The bound is not sharp.

Independent check: `tests/test_joint_rayleigh.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On the `2×2`
identity, CPQR returns both columns, `‖A_J x‖² = ‖x‖²` for `x = (1, 0)`,
the coefficient at `τ = 1`, `ρ = 0`, `k = 2`, `n = 2` equals `1/2`, and
`1/2 · ‖x‖² ≤ ‖A_J x‖²`. The test does not assert equality of the two
sides. It is not the theorem.

Non-claims: this is the Rayleigh form of the length-2 CPQR prefix. It
does not bound later pivots. A 2-column CPQR prefix is not a `k`-set for
`k > 2`. It does not close outcome 3. It is not a polynomial bound for
every orthogonal-row matrix. The census did not prove this. Problem 4.1
is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#51](https://github.com/tripp-smith/structured-column-selection/pull/51).

## Phase AM joint third pivot (2026-10-30, contract)

Iteration AM. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AL gives the Rayleigh coefficient
`μ = k (1 - ρ^2) / (2 τ^2 n)` on the length-2 CPQR prefix, the reciprocal
of `B = 2 τ^2 n / (k (1 - ρ^2))`. This phase adds the third CPQR pivot
by the same control flow as `equal_energy_cpqr_three_trace`, with those
joint bounds in place of equal column energy.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_three_trace`. Hypotheses of
`joint_cpqr_prefix_trace`, with `3 ≤ k` in place of `2 ≤ k`. `3 ≤ n`
follows from `orthogonalRows_le`.

Conclude:

```text
(selectedColGram A (cpqrIterate A 3)).det ≠ 0 ∧
((selectedColGram A (cpqrIterate A 3))⁻¹).trace ≤
  (2 : ℝ) * τ ^ 2 * (n : ℝ) / ((k : ℝ) * (1 - ρ ^ 2)) +
    (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) *
      (((n : ℝ) - 2) / ((k : ℝ) - 2))
```

The constant is that expression. It is not replaced by a looser one.
It is not claimed sharp: on the `3×3` identity the inverse trace is `3`
and the formula at `τ = 1`, `ρ = 0`, `k = 3`, `n = 3` equals `5`.

Proof shape. `cpqrIterate_invariant` gives `(cpqrIterate A 2).card = 2`
and invertibility of that Gram, and invertibility of the length-3 Gram.
`joint_cpqr_prefix_trace` gives trace at most `B`. The first two pivots
are not rebuilt. `joint_cpqr_prefix_rayleigh` is the quadratic lower
bound with coefficient `μ`. `nextResidual_ge` still gives
`maxResidual A J ≥ (k - 2) / (n - 2)`. The third column energy is not
`k / n`. `milestoneE_leverage_sum` gives `n · min ≤ k`, so
`min ≤ k / n`, and the leverage hypothesis gives `max ≤ τ · min`. The
Schur residual is nonnegative (`residualSq_eq_schur`), so
`q ≤ ℓ_j ≤ τ k / n`. `inv_norm_sq_le_of_quad_lower` gives
`c ≤ q / μ`, hence `c ≤ (τ k / n) / μ = 2 τ^3 / (1 - ρ^2)`. `field_simp`
cancels `n` and `k`. The increment is at most
`(1 + 2 τ^3 / (1 - ρ^2)) · (n - 2) / (k - 2)`.
`append_inv_trace_increment`, `append_inv_trace_eq_insert`, and
`appendColumn_gram_det_eq_insert` are the lemmas used for the
equal-energy third step.

Independent check: `tests/test_joint_three.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On the `3×3`
identity, CPQR returns three columns, the Gram inverse trace is `3`,
the formula at `τ = 1`, `ρ = 0`, `k = 3`, `n = 3` equals `5`, and
`3 ≤ 5`. The test does not assert that the trace equals `5`. It is not
the theorem.

Non-claims: this is the third CPQR pivot under the joint leverage-ratio
and coherence hypothesis. It does not bound pivots after the third.
A 3-column prefix is not a bound for general `k`. It does not close
outcome 3. It is not a polynomial bound for every orthogonal-row matrix.
The constant is not claimed sharp. The census did not prove this.
Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3.

Phase PR and verification receipt:
[#52](https://github.com/tripp-smith/structured-column-selection/pull/52).

## Phase AN joint three-row CPQR (2026-10-30, contract)

Iteration AN. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AM bounds the inverse trace of the length-3 CPQR
prefix `cpqrIterate A 3`. When `k = 3`, that prefix is the full CPQR set.
This phase records that specialization. It copies the shape of
`equal_energy_cpqr_k3`.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_k3`. Hypotheses: `OrthogonalRows A`, `k = 3`,
`0 < n`, `1 ≤ τ`, `0 ≤ ρ < 1`, and the same leverage comparison and
coherence bound as `milestoneE_joint_cpqr_three_trace`.

Conclude:

```text
(cpqrSet A).card = 3 ∧
(selectedColGram A (cpqrSet A)).det ≠ 0 ∧
((selectedColGram A (cpqrSet A))⁻¹).trace ≤ B ∧
∀ x : Fin (cpqrSet A).card → ℝ,
  vecEnergy x ≤ vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) * B
```

where `B` is

```text
(2 : ℝ) * τ ^ 2 * (n : ℝ) / ((3 : ℝ) * (1 - ρ ^ 2)) +
  (1 + (2 : ℝ) * τ ^ 3 / (1 - ρ ^ 2)) * ((n : ℝ) - 2)
```

The constant is that expression. It is not replaced by a looser one.
`k - 2 = 1`, so the last factor of the three-pivot bound is `(n - 2)`.
It is not claimed sharp: on the `3×3` identity the inverse trace is `3`
and the formula at `τ = 1`, `ρ = 0`, `n = 3` equals `5`.

Proof shape. `orthogonalRows_le` gives `3 ≤ n` from `k = 3`.
`cpqrSet A = cpqrIterate A 3`. `milestoneE_joint_cpqr_three_trace` gives
`det ≠ 0` and trace at most the unspecialized bound; its signature takes
`2 ≤ n`, and `3 ≤ n` supplies that. Rewriting `k = 3` produces `B`.
`cpqrIterate_invariant` gives card 3. The Rayleigh conjunct is
`selectedCols_energy_mul_inv_trace_ge`: multiply by the trace bound.
That quadratic form is not re-proved.

Independent check: `tests/test_joint_k3.py`, in `fractions.Fraction`,
calling `structselect.cpqr`. On the `3×3` identity, CPQR returns three
columns, the Gram inverse trace is `3`, `B` at `τ = 1`, `ρ = 0`, `n = 3`
equals `5`, and for `x = (1, 0, 0)` one has `‖x‖² ≤ 5 ‖A_J x‖²`. The
test does not assert that the trace equals `5`. It is not the theorem.

Non-claims: for three rows, the joint leverage-ratio and coherence
hypothesis bounds the full CPQR set, not only a prefix. This is not a
bound for general `k`. It does not close outcome 3. Outcome 3 needs a
polynomial theorem for a static class at general `k`. Fixing `k = 3`
does not count, just as `k = 1` and `k = 2` do not count. It is not
sharp. It is not a polynomial bound for every orthogonal-row matrix.
The census did not prove this. Problem 4.1 is not solved. `MinDimLe`
stays outside outcome 3.

Phase PR and verification receipt:
[#53](https://github.com/tripp-smith/structured-column-selection/pull/53).

## Phase AO CPQR trace step (2026-10-30, contract)

Iteration AO. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AN bounds the full CPQR set only for `k = 3`.
This phase is the one-step recurrence that moves a prefix of length `t`
to length `t + 1`. The recurrence is not iterated here. No closed form
is derived. A product of `k` factors is not claimed.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_step`. Hypotheses: `OrthogonalRows A`, `1 ≤ t`,
`t < k`, `t < n`, `1 ≤ τ`, `0 ≤ B`,
`∀ i j, residualSq A ∅ i ≤ τ * residualSq A ∅ j`, and
`((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B`.
Coherence is not a hypothesis. It was used only to start the recurrence
at length 2.

Conclude:

```text
(selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
  B + (1 + (τ * (k : ℝ) / (n : ℝ)) * B) * (((n : ℝ) - t) / ((k : ℝ) - t))
```

The constant is that expression. It is not replaced by a looser one.
It is not claimed sharp: on the `3×3` identity the length-2 Gram is
`I₂` with inverse trace `2`. At `B = 2`, `τ = 1`, `k = 3`, `n = 3`,
`t = 2` the step bound equals `5`. The length-3 inverse trace is `3`,
and `3 ≤ 5`.

Proof shape, matching `equal_energy_cpqr_three_trace` with `t` and `B`
in place of the length-2 special case. `cpqrIterate_invariant` gives
`(cpqrIterate A t).card = t` and invertibility of that Gram when
`t ≤ k`, and invertibility of the length-`t + 1` Gram. Pivot selection
is not rebuilt. `selectedCols_energy_mul_inv_trace_ge` gives
`‖x‖² ≤ T ‖A_J x‖²` with `T` the current inverse trace. The Gram is
invertible and positive semidefinite, so `T > 0`. Then `μ = 1 / T` is a
Rayleigh lower bound. `T ≤ B` and the Schur quadratic form `q` is
nonnegative, so replacing `T` by `B` only increases the later upper
bound. `nextResidual_ge` gives `maxResidual A J ≥ (k - t) / (n - t)`.
The CPQR pivot attains that maximum and is strictly positive, so
`cpqrIterate A (t + 1) = insert j J`. `milestoneE_leverage_sum` gives
`n · min ≤ k`, hence `min ≤ k / n`, and the leverage hypothesis gives
`max ≤ τ · min`, so the pivot column energy is at most `τ k / n`.
`residualSq_eq_schur` writes the residual as `ℓ_j - q` with `q ≥ 0`, so
`q ≤ ℓ_j`. `inv_norm_sq_le_of_quad_lower` gives
`c ≤ q / μ = q · T ≤ ℓ_j · B ≤ (τ k / n) · B`.
`append_inv_trace_increment` and `append_inv_trace_eq_insert` are the
lemmas used for the length-3 step. The increment is at most
`(1 + (τ k / n) B) · (n - t) / (k - t)`.

Independent check: `tests/test_cpqr_step.py`, in `fractions.Fraction`,
calling `structselect.cpqr`. On the `3×3` identity, the length-2 Gram is
`I₂` with inverse trace `2`. At `B = 2`, `τ = 1`, `k = 3`, `n = 3`,
`t = 2` the step bound equals `5`. The length-3 inverse trace is `3`,
and `3 ≤ 5`. The test does not assert equality. It is not the theorem.

Non-claims: one CPQR pivot step under a leverage-ratio bound, assuming
a trace bound on the current prefix. Not a bound on the full `k`-set.
Not a polynomial bound. Does not close outcome 3. Coherence is not used.
The recurrence is not iterated here. Iterating the step multiplies by a
factor of size `O(τ k)`. This phase does not produce a polynomial. The
census did not prove this. Problem 4.1 is not solved. `MinDimLe`,
`k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#54](https://github.com/tripp-smith/structured-column-selection/pull/54).

## Phase AP CPQR trace recurrence (2026-10-30, contract)

Iteration AP. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AO is one step from a prefix of length `t` to
length `t + 1`. This phase iterates that step from the length-2 bound up
to any `2 ≤ t ≤ k`. No closed product is derived. The bound is not a
polynomial in `k`. This does not close outcome 3.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_trace_bound`. `jointTraceBound` is the iterated
majorant. Hypotheses: `OrthogonalRows A`, `2 ≤ k`, `2 ≤ n`, `1 ≤ τ`,
`0 ≤ ρ`, `ρ < 1`, the leverage comparison
`residualSq A ∅ i ≤ τ * residualSq A ∅ j` for all `i, j`, the coherence
bound
`|colInner A i j| ≤ ρ * sqrt(residualSq A ∅ i) * sqrt(residualSq A ∅ j)`
for `i ≠ j`, and `2 ≤ t ≤ k`. `orthogonalRows_le` gives `k ≤ n`, hence
`t ≤ n`. `k ≤ n` is not an extra hypothesis.

Conclude:

```text
(selectedColGram A (cpqrIterate A t)).det ≠ 0 ∧
((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ jointTraceBound k n τ ρ t ∧
∀ x : Fin (cpqrIterate A t).card → ℝ,
  vecEnergy x ≤
    vecEnergy (selectedCols A (cpqrIterate A t) *ᵥ x) * jointTraceBound k n τ ρ t
```

The constant is `jointTraceBound`. It is not replaced by a looser one.
At `2` it is `2 τ^2 n / (k (1 - ρ^2))`. The successor at `s + 1`, for
`s ≥ 2`, is

```text
B + (1 + (τ * k / n) * B) * ((n - s) / (k - s))
```

with `B = jointTraceBound k n τ ρ s`. That is the increment in
`milestoneE_joint_cpqr_step`. Each step multiplies the previous bound by
`1 + (τ k / n) (n - s) / (k - s)` and adds `(n - s) / (k - s)`. That
factor is `O(τ k)` near the last pivot. The resulting bound is not a
polynomial in `k`. No closed product is derived.

It is not claimed sharp. On the identity at `τ = 1` and `ρ = 0`, the
bound at `k = n = 2` equals `2` and the inverse trace is `2`. At
`k = n = 3` the bounds are `2` then `5` and the inverse trace is `3 ≤ 5`.
At `k = n = 4` the bounds are `2`, `5`, then `11` and the inverse trace
is `4 ≤ 11`.

Proof shape. Induction on `t`. The base `t = 2` is
`milestoneE_joint_cpqr_prefix_trace`, which gives `det ≠ 0` and the
length-2 trace bound. Coherence is used only there. If `2 ≤ s < k` and
the statement holds at `s`, then `s < n`, `1 ≤ s`, and
`0 ≤ jointTraceBound … s`. The length-2 value is nonnegative, and each
increment has a nonnegative coefficient when `s < k` and `s < n`.
`milestoneE_joint_cpqr_step` with `B = jointTraceBound … s` is the
successor clause. `selectedCols_energy_mul_inv_trace_ge` gives
`‖x‖² ≤ trace · ‖A_J x‖²`, and the trace is replaced by the bound.
That quadratic form is not re-proved. There is no separate `k = 3`
corollary. That case is already `milestoneE_joint_cpqr_k3`.

Independent check: `tests/test_cpqr_recurrence.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On identities with
`τ = 1` and `ρ = 0`, the `2×2` bound and inverse trace are both `2`. At
`k = n = 3` the bounds are `2` then `5` and the inverse trace is `3 ≤ 5`.
At `k = n = 4` the bounds are `2`, `5`, then `11` and the inverse trace
is `4 ≤ 11`. Equality of the trace and the bound is asserted only for the
`2×2` identity. The test is not the theorem.

Non-claims: for every prefix length `2 ≤ t ≤ k`, the CPQR Gram inverse
trace is at most `jointTraceBound`. This is not a polynomial in `k`. It
does not close outcome 3. It is not a bound for matrices outside the
leverage-ratio and coherence hypotheses. Outcome 3 needs a polynomial
theorem for a static class at general `k`. The census did not prove this.
Problem 4.1 is not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside
outcome 3. `k = 3` was already proved and is not re-opened here.

Phase PR and verification receipt:
[#55](https://github.com/tripp-smith/structured-column-selection/pull/55).

## Phase AQ tighter CPQR step (2026-10-30, contract)

Iteration AQ. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AO bounds one CPQR pivot step by
`B + (1 + (τ k / n) B) (n - t) / (k - t)`. The added copy of `B` is an
artifact of using `q ≤ ℓ`. This phase removes that copy. The old step
stays. This is one tighter step, not an iteration. It does not close
outcome 3.

Target in `StructuredColumnSelection/JointPairGram.lean`, re-exported as
`milestoneE_joint_cpqr_step_tight`. Same hypotheses as
`milestoneE_joint_cpqr_step`: `OrthogonalRows A`, `1 ≤ t`, `t < k`,
`t < n`, `1 ≤ τ`, `0 ≤ B`,
`∀ i j, residualSq A ∅ i ≤ τ * residualSq A ∅ j`, and
`((selectedColGram A (cpqrIterate A t))⁻¹).trace ≤ B`.
Coherence is not a hypothesis.

Conclude:

```text
(selectedColGram A (cpqrIterate A (t + 1))).det ≠ 0 ∧
((selectedColGram A (cpqrIterate A (t + 1)))⁻¹).trace ≤
  (1 + (τ * (k : ℝ) / (n : ℝ)) * B) * (((n : ℝ) - t) / ((k : ℝ) - t))
```

There is no standalone `B +` in front. The constant is that expression.
It is not replaced by a looser one. It is not called sharp in general.
On the `3×3` identity the length-2 Gram is `I₂` with inverse trace `2`.
At `B = 2`, `τ = 1`, `k = n = 3`, `t = 2` the new bound equals `3` and
the old one equals `5`. The length-3 inverse trace is `3`. The identity
trace is `3`.

Proof shape. The argument follows `joint_cpqr_step` through
`c ≤ q * T`. Then `q = ℓ - residual` with `ℓ = v ⬝ᵥ v` and
`residual = ℓ - q`, so `c ≤ T * (ℓ - residual)`. Hence
`1 + c ≤ 1 + T * ℓ - T * residual` and
`(1 + c) / residual ≤ (1 + T * ℓ) / residual - T`. Adding the current
trace cancels `T`:
`T + (1 + c) / residual ≤ (1 + T * ℓ) / residual`.
Since `residual ≥ r_min > 0` with `r_min = (k - t) / (n - t)` and
`1 + T * ℓ ≥ 0`, this is at most `(1 + T * ℓ) / r_min`. Then `T ≤ B`
and `ℓ ≤ τ k / n` give
`(1 + (τ k / n) * B) * (n - t) / (k - t)`.
The proof does not return to `q ≤ ℓ`. `append_inv_trace_increment`,
`append_inv_trace_eq_insert`, and the determinant stay as in
`joint_cpqr_step`. The final addition of `T` and the ratio is the
cancelled form, not `B` plus the ratio.

Independent check: `tests/test_cpqr_step_tight.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On the `3×3`
identity, the length-2 inverse trace is `2`. The tight bound at
`B = 2`, `τ = 1`, `k = n = 3`, `t = 2` equals `3`. The length-3
inverse trace equals `3`. The old bound `2 + (1 + 2) * 1` equals `5`,
and `3 < 5`. The test is not the theorem.

Non-claims: tighter than `milestoneE_joint_cpqr_step` by one copy of
the current trace. Still one step. Not an iteration. Not a polynomial
bound. Does not close outcome 3. Coherence is not used. The recurrence
is not iterated here. The census did not prove this. Problem 4.1 is
not solved. `MinDimLe`, `k = 1`, and `k = 2` stay outside outcome 3.

Phase PR and verification receipt:
[#56](https://github.com/tripp-smith/structured-column-selection/pull/56).

## Phase AR square equal-leverage CPQR trace (2026-10-30, contract)

Iteration AR. Outcomes 1 and 3 stay open.

Route checkpoint. Phase AQ removes one copy of the current trace from a
single CPQR pivot step. For leverage ratio `τ > 1` the recurrence
`T ↦ 1 + τ T` is still exponential. The wide adverse family is outside
this class. This phase treats only square matrices (`n = k`) whose
column energies are equal, so the leverage comparison uses ratio `1`.
A `k = 3`-only or square-only (`n = k`) bound does not close outcome 3.

Target in `StructuredColumnSelection/JointPairGram.lean` as
`joint_square_equal_trace`, re-exported as
`milestoneE_joint_square_equal_trace`. Hypotheses: `OrthogonalRows A`
for `A : Matrix (Fin k) (Fin k) ℝ`, so `n = k` definitionally, `2 ≤ k`,
`0 ≤ ρ < 1`, equal column energies
`∀ i j, residualSq A ∅ i ≤ residualSq A ∅ j`, and normalized coherence
`|colInner A i j| ≤ ρ √(residualSq A ∅ i) √(residualSq A ∅ j)` for
`i ≠ j`.

Conclude:

```text
(cpqrSet A).card = k ∧
(selectedColGram A (cpqrSet A)).det ≠ 0 ∧
((selectedColGram A (cpqrSet A))⁻¹).trace ≤
  (k : ℝ) - 2 + 2 / (1 - ρ ^ 2) ∧
∀ x, vecEnergy x ≤
  vecEnergy (selectedCols A (cpqrSet A) *ᵥ x) *
    ((k : ℝ) - 2 + 2 / (1 - ρ ^ 2))
```

`cpqrSet A = cpqrIterate A k`. The coefficient is that expression. It
is not `jointTraceBound`. It is not claimed sharp for `ρ > 0`. On the
identity at `ρ = 0` the bound equals `k`, and the inverse trace equals
`k`. For `k = 2` the bound is `2`. For `k = 3` it is `3`. For `k = 4`
it is `4`.

Proof shape. Induct on the prefix length with `Nat.le_induction` from
`2`. For `2 ≤ t ≤ k`, `selectedColGram A (cpqrIterate A t)` is
invertible and its inverse trace is at most
`(t : ℝ) - 2 + 2 / (1 - ρ ^ 2)`. The length-2 case calls
`joint_cpqr_prefix_trace` at `τ = 1` and `n = k`. Equal energies give
`residualSq A ∅ i ≤ 1 * residualSq A ∅ j`. The prefix bound
`2 * 1 ^ 2 * k / (k * (1 - ρ ^ 2))` equals `2 / (1 - ρ ^ 2)`, which is
`(2 : ℝ) - 2 + 2 / (1 - ρ ^ 2)`. Each later step calls
`joint_cpqr_step_tight` at `τ = 1` with that prefix bound `B`. Because
`n = k` and `t < k`, the step factor
`(1 + (1 * k / k) B) * ((k - t) / (k - t))` equals `1 + B`, which is
the bound at length `t + 1`. For `ρ = 0` and `τ = 1` the tight step is
`T ↦ 1 + T`, so `k - 2` steps from the length-2 bound `2` give `k`.
Specialize at `t = k`. The card is `cpqrSet_card_eq`. The Rayleigh
conjunct is `selectedCols_energy_mul_inv_trace_ge`, multiplying the
trace inequality by the nonnegative image energy. `jointTraceBound`,
`milestoneE_joint_cpqr_step`, and `milestoneE_joint_cpqr_step_tight`
stay as they are. There is no general-`τ` closed form.

Independent check: `tests/test_square_equal_trace.py`, in
`fractions.Fraction`, calling `structselect.cpqr`. On the `k × k`
identity at `ρ = 0`, the bound and the CPQR-set Gram inverse trace are
both `3` when `k = 3` and both `4` when `k = 4`. Column energies of the
identity are equal, so the leverage ratio is `1`, and off-diagonal
inner products are `0`, so coherence `0` is admissible. The test is not
the theorem.

Non-claims: square and equal-leverage only. Not a polynomial bound for
rectangular matrices or for leverage ratio `τ > 1`. Not a polynomial
bound for every orthogonal-row matrix. Does not close outcome 3. For
`τ > 1` the recurrence `T ↦ 1 + τ T` is still exponential. The wide
adverse family is outside this class. Not claimed sharp for `ρ > 0`.
The census did not prove this. Problem 4.1 is not solved.

Phase PR and verification receipt:
[#57](https://github.com/tripp-smith/structured-column-selection/pull/57).
