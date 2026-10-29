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
