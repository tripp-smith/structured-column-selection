# Findings

## Phase 1 (Milestone A) delivered

Working with a `k × n` matrix `A` satisfying `A Aᵀ = I` is equivalent to
working with `Q := Aᵀ` satisfying `Qᵀ Q = I`. Selected `k × k` column
blocks and their Gram matrices are available as Lean definitions.

## Phase 2 (Milestone B) delivered

If `A Aᵀ = I`, the squared maximal minors form a finitely supported
probability distribution on the `k`-subsets of columns:

```text
∑_{|J|=k} det(A_J)² = 1.
```

## Phase 3 (Milestone C) delivered

The finite inverse-Gram identity is

```text
∑_{|J|=k} adj(A_J A_Jᵀ) = (n - k + 1) I
```

when `A Aᵀ = I`. More generally, without orthogonality,

```text
∑_{|J|=k} adj(A_J A_Jᵀ) = (n - k + 1) adj(A Aᵀ).
```

The proof deletes one row, applies Cauchy–Binet to the resulting
`(k-1)×k` and `(k-1)×n` products, and counts how many `k`-sets contain
each `(k-1)`-set (`n-k+1` of them).

The adjugate identity is distinct from
`∑ det(A_J)² (A_J A_Jᵀ)⁻¹`: these are not equal without additional support
conditions. Mathlib's matrix inverse is zero on
singular blocks, which would drop nonzero adjugate contributions. On
the running `2×3` witness the singular pair `{1,2}` contributes
`[[1,0],[0,0]]`; omitting it would break the identity.

Independent check on

```text
A = [ 1  0  0 ]
    [ 0  3/5 4/5 ]
```

the three adjugates are `[[9/25,0],[0,1]]`, `[[16/25,0],[0,1]]` and
`[[1,0],[0,0]]`, summing to `2 I`. The same arithmetic is repeated in
`tests/test_inverse_gram.py`.

## Phase 4 (Milestone D) delivered

Taking traces in the Milestone C identity gives the finite expectation

```text
∑_{|J|=k} tr(adj(A_J A_Jᵀ)) = k(n - k + 1)
```

when `A Aᵀ = I`. On an invertible block this summand is
`det(A_J)² ‖A_J⁻¹‖_F²`. A finitary Markov inequality then bounds the
volume mass of sets whose inverse-Frobenius energy exceeds
`k(n-k+1)/δ` by `δ`. Because `‖·‖_2 ≤ ‖·‖_F`, the same tail controls
the spectral quantity in Theorem R1 on the invertible locus.

The probability layer is a weighted sum over `Finset (Fin n)`, not a
measure-theoretic random variable.

Independent check: the `2×3` traces are `34/25`, `41/25` and `1`,
summing to `4 = 2·(3-2+1)`.

## Phase 5 (Milestone E structural CPQR) delivered

Ordinary CPQR is defined by repeatedly inserting the unused column of
largest Gram-determinant residual, breaking ties by the smallest
index. Empty residuals are leverage scores and sum to `k` when
`A Aᵀ = I`. A first pivot maximises that empty residual and therefore
has leverage at least `k / n`. On an orthogonal-row matrix the
algorithm cannot stop early: it returns exactly `k` columns.

For `k = 1` the first-pivot average is already the selected volume:
`volumeWeight A (cpqrSet A) ≥ n⁻¹`. The corresponding 1×1 inverse
magnitude is at most `√n`, matching the workshop scale.

Independent residuals after a full-rank set `J` sum to `k - #J`. The
next unused residual is therefore at least `(k-#J)/(n-#J)`, and the
product of CPQR pivot residuals gives
`volumeWeight A (cpqrSet A) ≥ 1 / C(n,k)`. That factor is exponential
in `k` when `n ≈ 2k` and is not a polynomial inverse-norm bound.

On the running `2×3` frame it selects `{0,2}`, with

```text
‖A_J⁻¹‖₂ = 5/4,    √(k(n-k+1)) = 2,    r_CPQR = 5/8.
```

A Python census (`structselect/census.py`,
`experiments/census_seed0.json`) records `r_CPQR` on Haar/Stiefel,
Hadamard, Fourier, leverage-skew, near-duplicate, and orthogonalized
Kahan-like frames. On the seed-0 sweep the worst ratio is `2/3`
(Hadamard `3×8`). That is a recorded witness, not a polynomial bound
and not a counterexample.

Wave 3 adds contraction and last-residual lemmas
(`milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`,
`milestoneE_last_residual_ge`). They constrain the residual-to-`σ_min`
gap and are not a joint `poly(n,k)` inverse-norm bound.

Wave 1 (`experiments/census_wave1_*_seed1.json`) adds Mercedes-Benz /
simplex / Paley / icosahedral ETFs, clustered near-parallels after
`row_orthonormalize`, Haar growth with `k ≤ 12`, and block-diagonal
ETF copies. Every recorded matrix had `AAᵀ ≈ I`. The worst ratio is
`√3/2` on the Mercedes-Benz / simplex `2×3`. No sample had
`r_CPQR > 1`, and none reached the campaign's named polynomial
yardstick. The simplex family saturates both `1/C(n,k)` and
`σ_min = |det|` at `n = k+1` with inverse norm `√(k+1)`; that is a
witness that those two universal estimates are sharp, not a
`poly(n,k)` theorem and not a counterexample. Clustered
near-parallels die after orthonormalization, like Kahan.

The Fin-indexed Cauchy–Binet `powersetCard` form is now also named
`cauchyBinet`, matching
https://faabian.github.io/algebraic-combinatorics/docs/AlgebraicCombinatorics/CauchyBinet.html
including the empty-sum case `n < k → det(AB) = 0`.

## Phase 6 (triangular trace bound + certified `C = 1` witness) delivered

The pivot-ordered CPQR Gram matrix factors as `G' = Uᵀ Δ U` with `U`
unit upper triangular, `|U i j| ≤ 1` (greedy maximality), and
`Δ = diag(δ)` the pivot residuals. Inverting `U` through the finite
Neumann series gives the Businger–Golub entry bound
`|S i j| ≤ 2^{j-i-1}` on `S = U⁻¹`, and the residual-energy ratio
`1/δ_l ≤ (n-l)/(k-l)` assembles into

```text
tr((G')⁻¹) ≤ (n - k + 1)(4^k + 6k - 1) / 9
```

(`milestoneE_pivot_gram_inv_trace_le`; Drmač–Gugercin /
Gu–Eisenstat style). This is polynomial in `n` but exponential in
`k`, so it is not a joint `poly(n,k)` inverse-norm bound and does
not close Milestone E.

A certified `C = 1` counterexample now exists: the rational `3×8`
frame `frame38` satisfies `AAᵀ = I` exactly, CPQR selects `{0,1,2}`
with strictly positive pivot margins, and an explicit rational test
vector certifies `‖A_J⁻¹‖₂ > √(k(n-k+1))`, i.e. `r_CPQR > 1`
(certified lower bound `r ≈ 1.030`). All three facts are
machine-checked in `SmallInstanceChecks.lean` (`native_decide`) and
re-certified independently over `Fraction` in
`tests/test_cpqr_r_gt_1.py`. This refutes only the ideal `C = 1`
workshop-scale bound: the certified inverse norm `≈ 4.37` is far
below the campaign's named polynomial `max(n³, k³, (k(n-k+1))²) =
512`, so Milestone E remains open. A `4×12` float record with
`r_CPQR ≈ 1.236` (`experiments/cpqr_r_gt_1_numeric_4_12.json`) is
numeric only and not certified.

SPEC §9 certification is automated in `structselect/certify.py`
(Cayley transform / rational Givens, pivot margins, inverse-norm test
vector). The published `frame38` rationals re-certify, as does a
Cayley re-parametrization of the same float matrix. That pipeline
does not close Milestone E.

## Phase 7 (parallel Milestone E merge) delivered

Five isolated tracks were merged. None of them is a joint
`poly(n,k)` inverse-norm bound, and Milestone E stays **OPEN**.

Proved (default axioms only; public names in `Theorems.lean`):

- residual antitone / rank-1 downdate
  (`milestoneE_residual_antitone`,
  `milestoneE_residual_insert_downdate`);
- Gram inverse-trace equals the sum of reciprocal leave-one-out
  residuals (`milestoneE_gram_inv_trace_eq_sum_inv_residual`),
  hence `σ_min(A_J) ≥ 1/√tr(G⁻¹)`
  (`milestoneE_sigma_min_ge_inv_sqrt_trace`);
- implicit CPQR factor `R Rᵀ = I`
  (`milestoneE_gsR_mul_transpose`);
- a polynomial inverse-trace bound **only if** Gram–Schmidt `U` is
  bidiagonal (`milestoneE_bidiagonal_U_inv_trace_le`). That is a
  hypothesis on `U`, not a class of matrices `A`, and not Path 1.

Path 2 trapezoidal search (`structselect/adverse.py`,
`experiments/cpqr_adverse_ladder_seed20260816.json`) is
polynomial-looking through `k = 8`. The worst recorded instance is
`(k,n)=(8,24)` with inverse norm `≈ 30.98`, `r_CPQR ≈ 2.66`
(`≈ 0.17%` of the named polynomial). `C = 1` witnesses exist;
no superpolynomial family was found.

## Phase 8 (Path 3 complementary-dimension class) delivered

After the certified `C = 1` witness `frame38`, the weakest extra
static hypothesis that turns the binomial volume bound into a
polynomial inverse-energy bound is dimensional: `min(k, n-k) ≤ d`.
No geometry is added. The class includes matrices with singular
`k`-sets.

Proved (default axioms only):

- `milestoneE_cpqr_inv_energy_le_choose`:
  `‖x‖² ≤ k · C(n,k) · ‖A_J x‖²` on the CPQR set. Exponential in
  `k` when `n ≈ 2k`; not a joint `poly(n,k)` bound.
- `milestoneE_cpqr_inv_energy_le_of_minDim`: on `min(k, n-k) ≤ d`,
  `‖x‖² ≤ k · n^d · ‖A_J x‖²`. Polynomial in `n` of degree `d`.
  Not Path 1.

Independent checks: frame23 has inverse `5/4` and `25/16 ≤ 6 =
2 · C(3,2) = 2 · 3^1`; frame12 has `25/16 ≤ 2`. A deeper ETF /
clustered census with these diagnostics is
`experiments/census_static_class_seed1.json` (worst recorded
`r_CPQR` still `√3/2` on the `2×3` simplex; no new `r > 1`).

Column incoherence and a leverage floor are recorded as static
predicates. They are narrower than `MinDimLe` and are not claimed
to be weakest. Milestone E remains **OPEN**: Path 1 is still the
unrestricted polynomial theorem.

## What remains open

Milestone E still requires one of: a polynomial CPQR theorem for
general `k`, a machine-checked counterexample past the named
polynomial, or a counterexample plus a stronger static class that
the project accepts as closing E. The complementary-dimension
class is a Path 3 theorem; it does not close Path 1. The
certified `frame38` witness kills only the ideal `C = 1` bound.
`R Rᵀ = I` is proved; a polynomial inverse-trace bound is proved
only under a bidiagonal hypothesis on `U`. Residual energy, the
binomial volume bound, and the triangular trace bound are proved;
the latter two are exponential in `k` and none of them closes E.
The Path 2 ladder through `k = 8` is a witness, not a theorem.
The `k = 1` volume bound is a genuine special case and also does
not close E. The later sections record outcome 2 and the CSSP bridge.
This repository does not claim to have solved all of Problem 4.1.
See `CHECKPOINT.md` for the reasoning log and the next-work queue.

## Column ℓ¹ budget on CPQR U (2026-10-23 phase)

Finite Lean result (`milestoneE_column_budget_S_abs_le_one`): if every
strict-upper column of U has absolute
sum at most one, back-substitution bounds each entry of S=U⁻¹ by one.
The triangular support then gives column energy ≤ j+1, and the existing
reciprocal-residual estimate gives inverse trace ≤ k(k+1)(n-k+1)/2.
This allows dense coupling and long edges; the budget is an extra
coefficient hypothesis, not a consequence established from AAᵀ=I.

Exact failed weakening: U=[[1,-1,-1],[0,1,-1],[0,0,1]] has entries bounded
by one, but U(2,1,1)ᵀ=e₂, so its inverse has entry 2. This is an
algebraic obstruction to that implication, not a CPQR/frame counterexample.
The rational dense and chain tests independently recompute solve energies;
the chain realizes ∑(j+1)=k(k+1)/2 at the coefficient level.
Milestone E remains open. Randomized volume sampling is unchanged.


## Actual inverse expectation audit (2026-10-24)

For all orthogonal-row frames the true volume-weighted inverse trace is
at most k(n-k+1). Equality holds if every k-block is nonsingular. The
adjugate proxy may carry a nonzero contribution at a zero-probability
singular block, so the unconditional equality stated in the original SPEC
is false. The original formula is retained there with this status annotation,
not silently replaced by a weaker target.

Exact witnesses: [1,0] has true expectation 1 and proxy 2. The running
frame23 has true expectation 3 and proxy 4. LDLᵀ/solve enumeration and an
independent signed-permutation determinant/cofactor formulation agree.
The actual nonsingular inverse-trace event, and its quantified inverse-energy
consequence, have volume mass at least 1-δ. Singular selections have mass zero.
These are direct finite-distribution statements, not adjugate event labels.
An efficient executable volume sampler remains missing. CPQR and CSSP remain
separate open tracks. This audit corrects the earlier claim that the minimum
publishable package was already complete.

## Reverse volume sampling phase (2026-10-24)

The literal finite reverse-deletion kernel has volume-sampling endpoint mass.
For retained S, let V(S) be the sum of volumes of its k-subsets. Each k-subset
survives deletion of exactly |S|-k elements, so
`∑ i∈S V(S.erase i) = (|S|-k)V(S)`. A weighted endpoint invariant telescopes
through zero-volume states without division by a zero child volume. Under
AAᵀ=I, the resulting (n-k)-step endpoint mass is exactly volumeWeight(J).

The efficient implementation uses rational LDLᵀ solves and downdates while
|S|>2k, then a projection Gram of at most 2k columns. Rejection weights are
`1-aᵢᵀ G_S⁻¹ aᵢ`; the dense finish uses their exact normalized values. The
backend bridge identifies V(S) with det(G_S) and these scores with determinant
ratios. Exact tests compare the factor/dense updates to independent determinants
and propagate the whole small-state distribution, including bounded failures.
They do not infer a law from empirical frequencies.

The ideal finite kernel is a Lean theorem. The Python program and its seeded
random source are not extracted/verified in Lean. Rational arithmetic can have
large bit growth. A proposal-budget failure is explicit and returns no sample.
CPQR characterization and the CSSP bridge remain open; the failed unconditional
inverse-expectation equality is still refuted, not restored by this sampler.

## Wide completion and prefix core (2026-10-24)

Every k×k real R with squared Frobenius energy ≤1 embeds unchanged as the first
k columns of a k×(k+k*t) Parseval frame for every natural t>0. Completion columns
have energy ≤k/t. The proof factors the PSD complement and repeats/scales its
columns; it does not assume an adverse family already exists.

For any upper-triangular leading block with nonzero diagonal, prefix projectors
are coordinate cuts and residuals are exact tail energies. Strict domination
of all later columns' tail energies by each leading diagonal square implies
the actual CPQR iterate chooses that prefix. These are finite entry conditions,
not a general inverse bound. The candidate rational diagonal stays above half
its initial scale for every m≥2 and i<m².

Public names are the five `milestoneE_wide_*` / `milestoneE_triangular_prefix_*`
outputs listed in README. Independent exact bordered-Gram computations check
every prefix at m=2,3; symbolic pair products certify row orthogonality without
materializing the wide frame. Direct multiplication checks closed-form inverse
witnesses at m=2,3,4. Larger scalar tests certify only scalar inequalities.
No all-parameter adverse-family theorem or joint-polynomial obstruction is
delivered in this section. The later adverse-family section records outcome 2.
CSSP and the full Problem 4.1 remain open.

## Explicit adverse family (2026-10-29)

For every integer `m ≥ 2`, `milestoneE_wide_adverse_family` gives a real
`m² × (m² + 32 m⁸)` orthogonal-row frame whose CPQR set is the first `m²`
columns and a selected coordinate with image energy exactly 1 and inverse
energy at least `((2m/3)(4/3)^(m-1))²`.
`milestoneE_cpqr_no_joint_polynomial` uses that frame: every positive
multiple of every power of `n+k+1` is beaten in inverse energy.
`milestoneE_cpqr_named_polynomial_obstruction` is the degree-4 case, so the
squared inverse energy exceeds `max(n³, k³, (k(n-k+1))²)²`.

This is a CPQR counterexample family. It does not say CPQR is polynomial on
every orthogonal-row matrix, and it does not solve Problem 4.1. Outcome 1
and outcome 3 remain open. Exact Python checks recompute bordered-Gram
residuals and cross-multiply the closed-form head against the scale; they
are not the theorem.

## CSSP bridge (2026-10-29)

`milestoneF_cssp_spectral` and `milestoneF_cssp_frobenius` compare the
coefficient reconstruction `A_J T`, with `T = (Q_Jᵀ)⁻¹ Qᵀ`, to `A`. For a
supplied factorization `A = U S Qᵀ + E` with `Qᵀ Q = 1` and invertible
`Q_J`, both norms satisfy `‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖`. The left-hand
norm is spectral or Frobenius; the coefficient is the spectral norm of
`Q_J⁻¹` in both theorems. The argument is the identity
`A - A_J T = E - E_J T`. It does not build a truncated SVD.

One exact rational example checks that identity and the squared Frobenius
comparison. That check is not the theorem. Outcomes 1 and 3 stay open.
Problem 4.1 is not solved, and CPQR is not claimed to be polynomial on
every orthogonal-row matrix.

## Weighted signed triple design (2026-10-30)

`milestoneE_triple_design` gives, for every `n`, an explicit tight design
`W Wᵀ = I` in `ℝ^(n+3)` with `4 (n+3)(n+2)(n+1)` columns, every column of
energy `1 / (4 (n+2)(n+1))`, and every pair of distinct columns at
normalized inner product at most `13/14`. Columns are
`(e_p + 2σ e_{q'} + 3τ e_{r'}) / √(56 (n+2)(n+1))` over distinct
coordinates `p, q', r'` chosen through `Fin.succAbove`; sign sums kill
every cross term in the row Gram matrix, and the coherence bound is an
integer argument (an inner product of two integer columns of squared
length `14` is an integer, and `±14` forces equal or opposite columns).
The constant `13/14` is attained by swapping the weights `1` and `2`.
The design is pairwise non-parallel, unlike the repeated filler block
of the outcome-2 frame. Its column energy is above the `1 / wideRepeats`
cap of `milestoneE_design_adverse_family`, so no adverse frame is built
from it in this phase, and no coherence bound on any orthogonal-row
frame is claimed. This does not close outcome 3.

## Symmetric completion bounds (2026-10-30)

`milestoneE_symmetric_completion` says that every `R` with `‖R‖_F² ≤ 1`
has a symmetric completion `C` with `R Rᵀ + C Cᵀ = I` such that
`⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`,
`(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and
`‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`. The matrix is the positive semidefinite
square root of `I - R Rᵀ`; the perturbation bound comes from
`(C + I)(C - I) = -R Rᵀ` and `‖(C + I) u‖² ≥ ‖u‖²` for `C ⪰ 0`, with
no spectral decomposition. This is a completion for the design frame.
No coherence bound on any frame is proved. This does not close
outcome 3.

## Design-padded adverse family (2026-10-30)

`milestoneE_design_adverse_family` says that the outcome-2 construction
does not need the repeated filler block. For every `m ≥ 2`, every
completion `C` with `R Rᵀ + C Cᵀ = I` of the triangular block `R`, and
every tight design `W` with `W Wᵀ = I` and column energy at most
`1 / wideRepeats m`, the frame `[R | C W]` has orthogonal rows, CPQR
takes the leading prefix, the image energy is `1`, and the inverse
energy is at least `wideGrowthLower m ^ 2`. The filler energy bound is
`‖C w‖² ≤ ‖C‖_F² ‖w‖² ≤ k ‖w‖²`. The repeated frame is the design
`(1/√t)[I ⋯ I]`. No bound on the normalized coherence of the resulting
columns is proved. This does not close outcome 3.

## Outcome-2 normalized coherence is 1 (2026-10-29)

`milestoneE_normalized_coherence_one` says that the outcome-2 frame
repeats a positive completion column. Two distinct columns are equal,
their normalized coherence is `1`, and the CPQR block still beats
`C (n + k + 1)^{2d}`. A class that requires every normalized ratio to
be at most some `ρ < 1` excludes this frame. The theorem does not give
a polynomial CPQR bound on a stricter ratio. Absolute inner-product
incoherence remains the phase-Z predicate. This does not close
outcome 3.

## Absolute incoherence does not restore a polynomial (2026-10-29)

`milestoneE_incoherent_no_joint_polynomial` says that for every `ρ > 0`,
some orthogonal-row frame with absolute off-diagonal inner products at
most `ρ` still has a CPQR block beating `C (n + k + 1)^{2d}`. The
outcome-2 columns have energy at most `1 / (2k)`. This predicate is not
the normalized coherence ratio, and `ρ = 0` remains outside the family.
This does not close outcome 3.

## Equal energy splits the third CPQR pivot (2026-10-29)

`milestoneE_equal_energy_third_pivot_split` gives an orthogonal-row
`3×6` frame with column energy `1/2`. Both rules take column `0` and
then column `2`. After `{0, 2}`, max-residual CPQR takes column `3` and
the increment pivot takes column `5`, so the selected sets are
`{0, 2, 3}` and `{0, 2, 5}`. Columns `0` and `2` have inner product
`-2/17`, so the orthogonal-block agreement does not apply. This does
not close outcome 3.

## Equal energy does not make every block agree (2026-10-29)

`milestoneE_equal_energy_block_pivot_split` gives an orthogonal-row
`3×6` frame with column energy `1/2`. Columns `0` and `1` have inner
product `31/100`. After that block, max-residual CPQR takes column `5`
and the increment pivot takes column `3`. Column `5` is orthogonal to
column `0`, so this block is not the two-column CPQR prefix. Equal
energy still makes an orthogonal block agree. This does not close
outcome 3.

## Orthogonal equal-energy block, same next pivot (2026-10-29)

`milestoneE_equal_energy_orthogonal_block_same_pivot` says that equal
column energy and a pairwise-orthogonal selected block make the next
max-residual CPQR pivot agree with the increment pivot. The selected
Gram is `(k / n)` times the identity, and the increment ratio
`(2e - r) / (e r)` decreases as the residual grows. A one-column block
is the agreement half of the equal-energy second pivot. The estimate
`‖G⁻¹ w‖² ≤ q / λ_min` exceeds the increment allowance at
`k = 3`, `n = 6`, `λ_min = 2/5` (`13/8 > 37/24`), so that estimate
does not finish a polynomial induction. This does not close outcome 3.

## Leverage ratio `32/13` splits the second pivot (2026-10-29)

`milestoneE_leverage_ratio_pivot_split` gives an orthogonal-row `2×5`
frame whose column energies lie in `[13/50, 16/25]`. The ratio of those
endpoints is `32/13`. Both rules take column `0` first. Every later
residual equals `1/4`, so max-residual CPQR takes column `1`, while the
increment ratios `89/16`, `65/16`, `73/16`, and `65/16` take column `2`.
Equal column energy still makes those second pivots agree. This witness
does not close outcome 3.

## Equal-energy three-row CPQR (2026-10-29)

`milestoneE_equal_energy_cpqr_k3` says that when `k = 3`, equal column
energy makes the full CPQR set have three columns, inverse trace at most
`5n - 12 + 6/n`, and `‖x‖² ≤ (5n - 12 + 6/n) ‖A_J x‖²`. The three-column
prefix is the whole set in this case. The same trace estimate, iterated
with `λ_min ≥ 1 / trace`, unrolls exponentially in `k`, so this does not
extend to general `k` and does not close outcome 3. Equal energy is
leverage ratio `1`, stricter than the weakest SPEC §10 class.

## Equal-energy three-column trace (2026-10-29)

`milestoneE_equal_energy_cpqr_three_trace` says that equal column energy
makes the CPQR three-column inverse trace at most
`2 (n - 1) / (k - 1)` plus one step controlled by the phase-S Rayleigh
quotient. The third residual is at least `(k - 2) / (n - 2)`, and the
coefficient `‖G⁻¹ v‖²` is at most `(k / n)` divided by that quotient.
This does not bound a `k`-set for `k > 3` and does not close outcome 3.
Equal energy is leverage ratio `1`, stricter than the weakest SPEC §10
class, and the adverse family is outside it.

## Equal-energy prefix Rayleigh (2026-10-29)

`milestoneE_equal_energy_cpqr_prefix_rayleigh` says that equal column
energy makes the CPQR two-column quadratic form at least
`(k - 1) / (2 (n - 1))` times `‖x‖²`. The second pivot residual is at
least the unused average `(k - 1) / (n - 1)`, and the smaller Gram
eigenvalue is at least half that residual. This replaces
`‖G⁻¹ v‖² ≤ trace(G⁻¹) · q` only at the two-column prefix. It does not
finish an induction, does not bound a `k`-set for `k > 2`, and does not
close outcome 3. Equal energy is leverage ratio `1`, stricter than the
weakest SPEC §10 class, and the adverse family is outside it.

## Equal-energy second pivot (2026-10-29)

`milestoneE_equal_energy_cpqr_prefix_trace` says that equal column energy
forces every column energy to `k / n`. The first CPQR pivot is column `0`.
On that singleton the inverse-trace ratio decreases as the residual
grows, so the second CPQR pivot equals the increment pivot. The
two-column inverse trace is at most `2 (n - 1) / (k - 1)`. The estimate
`‖G⁻¹ v‖² ≤ trace(G⁻¹) · q` does not close later pivots. Equal energy is
leverage ratio `1`, stricter than the weakest SPEC §10 class, and the
adverse family is outside it. This does not close outcome 3.

## Adverse family outside orthogonal columns (2026-10-29)

`milestoneE_wide_not_incoherent_zero` says that for every `m ≥ 2` the
outcome-2 frame is orthogonal across rows and has two leading columns
whose inner product is `-wideC m * (wideDiagNat m 0) ^ 2 ≠ 0`. The
phase-P CPQR bound does not apply to that frame. This does not close
outcome 3.

## Orthogonal-column CPQR (2026-10-29)

`milestoneE_incoherent_zero_cpqr_bound` says that pairwise orthogonal
columns of an orthogonal-row matrix are selected by max-residual CPQR.
Exactly `k` columns have energy `1`, the Gram is the identity, the
inverse trace is `k`, and `‖x‖² = ‖A_J x‖²`. Both quantities sit under
`k (n - k + 1)` and `1 + k (n - k)`. The class is read from `A`. It is
stricter than the SPEC §10 target, and the adverse family is outside
it. This does not close outcome 3.

## Zero-coefficient pivot (2026-10-29)

`milestoneE_zero_coeff_same_pivot` says that if the selected Gram is
invertible and every positive-residual unused column has coefficient
zero, the increment pivot and max-residual CPQR return the same column.
The ratio is then the reciprocal of the residual. Phase N shows that a
nonzero coefficient can separate the rules. This does not close
outcome 3.

## Pivot split (2026-10-29)

`milestoneE_increment_set_ne_cpqr` says there is an orthogonal-row
`2×5` matrix on which `incrementSet` and `cpqrSet` differ. Both rules
take column `0` first. CPQR then takes column `1`, because the residual
`2/5` is tied and the least index wins. The increment ratios are
`17/5` at column `1` and `29/10` at column `2`, so the increment pivot
takes column `2`. The sets are `{0, 1}` and `{0, 2}`. This does not
close outcome 1 or outcome 3.

## Increment set (2026-10-29)

`milestoneE_increment_set_bound` names the least-index column that
minimizes the inverse-trace increment and iterates it from the empty
block. The resulting set has `k` columns, invertible Gram, inverse trace
at most `k (n - k + 1)`, and satisfies
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. Max-residual CPQR is a different
rule. This does not close outcome 3. On the rational `2×3` frame the
empty-block scores are `1`, `25/9`, and `25/16`, so the first column is
`0`; the next scores pick column `2`. That check is not the theorem.

## Inverse spectral bound (2026-10-29)

`milestoneE_minimizing_inv_spectral_le` says that an orthogonal-row
matrix has some set of `k` columns whose Gram is invertible and which
satisfies `‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. The set is the increment
pivot from the inverse-trace induction. The argument uses that every
column submatrix is a contraction, so `G⁻¹ - I` is positive semidefinite
and the inverse trace drops by `k - 1` before it bounds the squared
operator norm. Max-residual CPQR is a different rule. This does not
close outcome 3. On the rational `2×3` frame, columns `{0, 2}` send
`(0, 1)` to a vector of energy `16/25`, and `1 + 2 · 1 = 3`; that check
is not the theorem.

## Inverse-trace induction (2026-10-29)

`milestoneE_minimizing_inv_trace_le` says that an orthogonal-row matrix
has some set of `k` columns whose Gram is invertible and whose inverse
trace is at most `k (n - k + 1)`. The set is built by starting from the
empty block and appending a column that meets the increment bound at
each step. Max-residual CPQR is a different rule. This is not a spectral
bound and it does not close outcome 3. On the rational `2×3` frame,
columns `{0, 2}` have inverse trace `1 + 25/16`, which is at most `4`;
that check is not the theorem.

## Inverse-trace growth step (2026-10-29)

`milestoneE_inv_trace_growth_step` says that if an invertible selected
Gram on `t < k` columns already has inverse trace at most
`t (n - t + 1) / (k - t + 1)`, some column outside the block can be
appended so the new inverse trace is at most
`(t + 1) (n - t) / (k - t)`. The step uses the best unused increment
from phase I and the one-column update from phase H. It does not say
that the max-residual CPQR pivot takes this step, and it does not
finish the induction from the empty block. This is not a polynomial
inverse bound and it does not close outcome 3. On the rational `2×3`
frame, column 0 has trace `1 ≤ 3/2`, and appending column 2 produces
trace `1 + 25/16 ≤ 4`; that check is not the theorem.

## Best-column increment (2026-10-29)

`milestoneE_best_column_increment_le` says that if the selected Gram is
invertible and fewer than `k` columns are selected, some unused column has
positive residual and inverse-trace increment at most
`((n - t) + trace(G⁻¹) - t) / (k - t)`. The estimate averages the
numerators `1 + ‖G⁻¹ Bᵀ a_j‖²` over the unused columns whose residuals are
positive. Standard CPQR maximizes the residual and does not minimize this
ratio. This is not a polynomial inverse bound and it does not close
outcome 3. On the rational `2×3` frame with `J = {0}`, column 2 has ratio
`25/16` and the comparison is `2`; that check is not the theorem.

## Inverse-trace increment (2026-10-29)

`milestoneE_append_inv_trace_increment` says that appending a column `v`
to an invertible column block `B` increases the Gram inverse trace by
`(1 + ‖(Bᵀ B)⁻¹ Bᵀ v‖²) / residual`. The denominator is the Schur
complement `‖v‖² - (Bᵀ v) ⬝ (Bᵀ B)⁻¹ (Bᵀ v)`. Standard CPQR does not
choose the column that minimizes this ratio. This is not a polynomial
inverse bound and it does not close outcome 3. An exact `2×2` inverse
trace on columns `(1,0)` and `(0,3/5)` equals `1 + 25/9`; that check is
not the theorem.

## Wide leverage escape (2026-10-29)

`milestoneE_wide_leverage_escape` says that for every `τ ≥ 0` some frame
from the outcome-2 family has two column energies with ratio greater than
`τ`, and in fact greater than `8 m²`. The family therefore lies outside
every fixed leverage-ratio class. This is not a polynomial theorem for
matrices whose column energies are within a fixed ratio, and it does not
close outcome 3. Exact triangular and LDL energies at `m = 2, 3, 4`
meet the same `8 m²` comparison; that check is not the theorem.
