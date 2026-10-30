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

## Two-extra-column CPQR trace (2026-10-30)

`milestoneE_joint_codim_two_trace` is `n = k + 2` only. Under equal
column energies and coherence at most `ρ < 1`, an orthogonal-row
`k × (k + 2)` matrix has CPQR inverse trace at most
`(k - 1)(k + 2) / (1 - ρ ^ 2) + (k - 1) k (k + 1) / 6 - 1`, and the
same factor bounds the Rayleigh form. At `ρ = 0` and `k = 2` both sides
equal `4`; at `k = 3` the majorant is `9` and the bound is `13`; at
`k = 4` the majorant is `15` and the bound is `27`.

`tests/test_codim_two.py` checks those rationals with
`fractions.Fraction`. The check is not the theorem. It bounds the
majorant at `n = k + 2`. It is not itself a CPQR inverse trace.

This is two extra columns, not a general `n`. It is a polynomial in `k`
and in `1 / (1 - ρ ^ 2)`, not a polynomial theorem for general `n`.
One extra column stays phase AW. Phase AU still says the majorant at
`n = 2k` is not polynomial. Phase AV still says the square trace equals
`k`. Outcome 3 stays open. This does not close outcome 1. Problem 4.1
is not solved, and this phase does not claim that CPQR is polynomial on
orthogonal-row matrices, or on every equal-leverage matrix.

## Codimension-one CPQR trace (2026-10-30)

`milestoneE_joint_codim_one_trace` is `n = k + 1` only. Under equal
column energies and coherence at most `ρ < 1`, an orthogonal-row
`k × (k + 1)` matrix has CPQR inverse trace at most
`(k + 1)(k + 2) + 2k / (1 - ρ ^ 2)`, and the same factor bounds the
Rayleigh form. At `ρ = 0` the majorant values are `3` for `k = 2` and
`6` for `k = 3`; the bounds are `16` and `26`.

`tests/test_codim_one.py` checks those rationals with
`fractions.Fraction`. The check is not the theorem. It bounds the
majorant at `n = k + 1`. It is not a CPQR inverse trace by itself.

This is one extra column, not a general `n`. It is a polynomial in `k`
and in `1 / (1 - ρ ^ 2)`, not a polynomial theorem for general `n`.
Phase AU still says the majorant at `n = 2k` is not polynomial. Phase AV
still says the square trace equals `k`. Outcome 3 stays open. This does
not close outcome 1. Problem 4.1 is not solved, and this phase does not
claim that CPQR is polynomial on orthogonal-row matrices, or on every
equal-leverage matrix.

## Square CPQR trace (2026-10-30)

`milestoneE_square_cpqr_trace_eq` is square only. For an orthogonal-row
`k × k` matrix, `cpqrSet` is every column, `selectedColGram` is `1`, and
the inverse trace equals `k`. The selected columns preserve Euclidean
energy. Phase AR's bound `(k : ℝ) - 2 + 2 / (1 - ρ ^ 2)` equals this
value at `ρ = 0`, which is admissible because column inner products
vanish. Phase AR stays an inequality.

`tests/test_square_trace_eq.py` checks the `k = 2` and `k = 3` identities
and a `2 × 2` rotation with rows `(3/5, -4/5)` and `(4/5, 3/5)`, using
`fractions.Fraction` and `structselect.cpqr`. The rows of the rotation
are orthonormal and the column inner product is `0`. The check is not
the theorem.

Rectangular matrices are not included. The equal-leverage majorant at
`n = 2k` is still not a polynomial. A square-only bound does not close
outcome 3. This does not close outcome 1. Problem 4.1 is not solved, and
this phase does not claim that CPQR is polynomial on orthogonal-row
matrices.

## Equal-leverage majorant (2026-10-30)

`milestoneE_joint_equal_majorant_not_polynomial` lower-bounds
`jointTraceBoundTight` at `τ = 1`, `ρ = 0`, and `n = 2k`. For every
degree `d` and every `C > 0`, some `k ≥ 2` has
`C (3k + 1)^{2d} < jointTraceBoundTight k (2k) 1 0 k`. The majorant is
at least `2^k / k`. At `k = 4` the values are `4`, then `9`, then
`55/2`, and `2^4 / 4 = 4 ≤ 55/2`.

`tests/test_equal_majorant.py` checks those rationals with
`fractions.Fraction`. The check is not the theorem. It lower-bounds the
majorant only. It is not a CPQR inverse trace.

Phase AR's square bound at `n = k` and `τ = 1` is unchanged and still
polynomial. This does not place any matrix in the joint class. Outcome 3
stays open: a lower bound on this majorant is not a matrix
counterexample, and this majorant is not a polynomial theorem for the
equal-leverage class. This does not close outcome 1. Problem 4.1 is not
solved, and this phase does not claim that CPQR is polynomial on
orthogonal-row matrices.

## Tight majorant growth (2026-10-30)

`milestoneE_joint_trace_majorant_not_polynomial` lower-bounds
`jointTraceBoundTight` along `n = k`, `τ = 2`, `ρ = 0`. For every
degree `d` and every `C > 0`, some `k ≥ 2` has
`C (2k + 1)^{2d} < jointTraceBoundTight k k 2 0 k`. The majorant is at
least `2^{k+1}`. At `k = 4` the values are `8`, then `17`, then `35`,
and `2^5 = 32 ≤ 35`.

`tests/test_majorant_growth.py` checks those rationals with
`fractions.Fraction`. The check is not the theorem. It lower-bounds the
majorant only. It is not a CPQR inverse trace.

The square identity at `τ = 1` has inverse trace `k`. The phase-AI
census did not see `r_CPQR` growth. This does not place any matrix in
the joint class. Outcome 3 stays open because a lower bound on this
majorant is not a matrix counterexample inside the joint class, and the
majorant is not a polynomial theorem. The loose majorant is untouched.
This does not close outcome 1. Problem 4.1 is not solved, and this phase
does not claim that CPQR is polynomial on orthogonal-row matrices.

## Tight CPQR trace recurrence (2026-10-30)

`milestoneE_joint_cpqr_trace_bound_tight` iterates `joint_cpqr_step_tight`,
not the loose step, from the length-2 prefix up to any `2 ≤ t ≤ k`.
Orthogonal rows, `2 ≤ k`, `2 ≤ n`, a leverage ratio at most `τ`, and
normalized coherence at most `ρ < 1` give an invertible Gram
`selectedColGram A (cpqrIterate A t)` whose inverse trace is at most
`jointTraceBoundTight k n τ ρ t`, and the same factor bounds the Rayleigh
form. The successor is `(1 + (τ k / n) B) (n - s) / (k - s)` with no
added copy of `B`. Coherence is used only at length 2.

On the identity at `τ = 1`, `ρ = 0`, `n = k`, the tight values are
`2, 3, 4, ...` while the loose values are `2, 5, 11, ...`. At
`k = n = 3` the bounds are `2` then `3` and the prefix inverse traces are
`2` and `3`. The loose successor at `t = 3` is `5`, and `3 < 5`. At
`k = n = 4` the bounds are `2`, `3`, `4` and the inverse traces equal
those numbers. The loose value at `t = 4` is `11`, and `4 < 11`. Equality
of trace and bound is asserted only for those identity checks, not in
general.

`tests/test_cpqr_recurrence_tight.py` checks those rationals with
`structselect.cpqr`. The check is not the theorem.

The recurrence is not a polynomial in `k`. When `n = k` and `τ > 1`, each
pivot sends `B` to `1 + τ B`, which is still exponential in the number of
pivots. When `n > k`, the factor `(n - s) / (k - s)` is not a polynomial
bound. This does not close outcome 3. The loose recurrence
`jointTraceBound` is unchanged. Phase AR remains the square equal-leverage
closed form. Problem 4.1 is not solved, and this phase does not claim
that CPQR is polynomial on orthogonal-row matrices.

## Square equal-leverage CPQR trace (2026-10-30)

`milestoneE_joint_square_equal_trace` is square and equal-leverage only.
For an orthogonal-row `k × k` matrix with equal column energies and
normalized coherence at most `ρ < 1`, the CPQR Gram inverse trace is at
most `(k : ℝ) - 2 + 2 / (1 - ρ ^ 2)`, and the same factor bounds the
Rayleigh form. The length-2 base is `2 / (1 - ρ ^ 2)`. Each later tight
step adds `1`. At `ρ = 0` on the identity the bound equals `k`, and the
inverse trace equals `k`.

`tests/test_square_equal_trace.py` checks the `k = 3` and `k = 4`
identities at `ρ = 0` with `structselect.cpqr`. The check is not the
theorem.

This is not a polynomial bound for rectangular matrices or for leverage
ratio `τ > 1`. For `τ > 1` the recurrence `T ↦ 1 + τ T` is still
exponential. The wide adverse family is outside this class. A square-only
(`n = k`) bound does not close outcome 3. The bound is not claimed sharp
for `ρ > 0`. Problem 4.1 is not solved, and this phase does not claim
that CPQR is polynomial on orthogonal-row matrices.

## Tighter CPQR trace step (2026-10-30)

`milestoneE_joint_cpqr_step_tight` has the same hypotheses as
`milestoneE_joint_cpqr_step`. The next inverse trace is at most
`(1 + (τ k / n) B) · (n - t) / (k - t)`, with no standalone `B +`.
The proof keeps `c ≤ q · T`, writes `q = ℓ - residual`, and cancels
the current trace `T` against `-T` in `(1 + c) / residual`. It does
not return to `q ≤ ℓ`.

On the `3×3` identity the new bound at `B = 2`, `τ = 1`, `k = n = 3`,
`t = 2` equals `3` and the old bound equals `5`. The length-2 inverse
trace is `2`. The length-3 inverse trace is `3`. The identity trace is
`3`. The new bound is not claimed sharp in general.

`tests/test_cpqr_step_tight.py` checks those rationals with
`structselect.cpqr`. The check is not the theorem.

This is tighter than `milestoneE_joint_cpqr_step` by one copy of the
current trace. It is still one step. It is not an iteration. It is not
a polynomial bound. It does not close outcome 3. Problem 4.1 is not
solved, and this phase does not claim that CPQR is polynomial on
orthogonal-row matrices.

## CPQR trace recurrence (2026-10-30)

`milestoneE_joint_cpqr_trace_bound` iterates `milestoneE_joint_cpqr_step`
from the length-2 prefix up to any `2 ≤ t ≤ k`. Orthogonal rows, `2 ≤ k`,
`2 ≤ n`, a leverage ratio at most `τ`, and normalized coherence at most
`ρ < 1` give an invertible Gram `selectedColGram A (cpqrIterate A t)`
whose inverse trace is at most `jointTraceBound k n τ ρ t`, and
`‖x‖² ≤ jointTraceBound k n τ ρ t · ‖selectedCols A (cpqrIterate A t) x‖²`.

`orthogonalRows_le` supplies `k ≤ n`, hence `t ≤ n`. The length-2 case is
`milestoneE_joint_cpqr_prefix_trace`. Coherence is used only there. If
`2 ≤ s < k` and the inverse trace at `s` is at most `jointTraceBound … s`,
then `s < n`, `1 ≤ s`, and that bound is nonnegative. The step theorem
with `B = jointTraceBound … s` is the successor value. The Rayleigh
conjunct is `selectedCols_energy_mul_inv_trace_ge`.

Each step multiplies the previous bound by
`1 + (τ k / n) (n - s) / (k - s)` and adds `(n - s) / (k - s)`. That factor
is `O(τ k)` near the last pivot. The bound is not a polynomial in `k`.
No closed product is derived.

`tests/test_cpqr_recurrence.py` runs `structselect.cpqr` on identities
with `τ = 1` and `ρ = 0`. At `k = n = 2` the bound and the inverse trace
are both `2`. At `k = n = 3` the bounds are `2` then `5`, and the inverse
trace is `3 ≤ 5`. At `k = n = 4` the bounds are `2`, `5`, then `11`, and
the inverse trace is `4 ≤ 11`. Equality of the trace and the bound is
asserted only for the `2×2` identity. The check is not the theorem.

This does not close outcome 3. `k = 3` was already
`milestoneE_joint_cpqr_k3`. Problem 4.1 is not solved, and this phase does
not claim that CPQR is polynomial on orthogonal-row matrices.

## CPQR trace step (2026-10-30)

`milestoneE_joint_cpqr_step` moves a CPQR prefix of length `t` to length
`t + 1`. Orthogonal rows, `1 ≤ t < k`, `t < n`, a leverage ratio at most
`τ`, and an inverse-trace bound `B` on `cpqrIterate A t` give an
invertible Gram at `t + 1` whose inverse trace is at most

`B + (1 + (τ k / n) B) · (n - t) / (k - t)`.

The constant was not weakened. The current inverse trace `T` is positive,
so `μ = 1 / T` is a Rayleigh lower bound. `T ≤ B` and the Schur form `q`
is nonnegative, so the later upper bound may replace `T` by `B`. The
residual average is `(k - t) / (n - t)`, and the pivot column energy is
at most `τ k / n`. Coherence is not a hypothesis. It was used only to
start a recurrence at length 2.

`tests/test_cpqr_step.py` runs `structselect.cpqr` on the `3×3` identity.
The length-2 Gram is `I₂` and its inverse trace is `2`. At `B = 2`,
`τ = 1`, `k = 3`, `n = 3`, `t = 2` the step bound equals `5`. The
length-3 inverse trace is `3`, and `3 ≤ 5`. The check does not assert
equality. It is not the theorem.

Iterating the step multiplies by a factor of size `O(τ k)`. This phase
does not iterate the recurrence and does not produce a polynomial. It
does not bound the full `k`-set. It does not close outcome 3. Problem
4.1 is not solved, and this phase does not claim that CPQR is polynomial
on orthogonal-row matrices.

## Joint three-row CPQR (2026-10-30)

`milestoneE_joint_cpqr_k3` specializes `milestoneE_joint_cpqr_three_trace`
to `k = 3`. Then `cpqrSet A = cpqrIterate A 3`, so the length-3 prefix is
the full CPQR set. `orthogonalRows_le` gives `3 ≤ n`. Because `k - 2 = 1`,
the last factor of the three-pivot bound is `(n - 2)`. The inverse trace
and the inverse energy are at most

`2 τ^2 n / (3 (1 - ρ^2)) + (1 + 2 τ^3 / (1 - ρ^2)) · (n - 2)`.

The constant was not weakened. The Rayleigh conjunct is
`selectedCols_energy_mul_inv_trace_ge`.

`tests/test_joint_k3.py` runs `structselect.cpqr` on the `3×3` identity.
CPQR returns three columns. The Gram inverse trace is `3`. The bound at
`τ = 1`, `ρ = 0`, `n = 3` equals `5`, and for `x = (1, 0, 0)` one has
`‖x‖² ≤ 5 ‖A_J x‖²`. The check does not assert that the trace equals `5`.
On that matrix the inverse trace is `3` and the bound is `5`. The constant
is not claimed sharp. The check is not the theorem.

This is not a bound for general `k`. Fixing `k = 3` does not close
outcome 3. Outcome 3 needs a polynomial theorem for a static class at
general `k`. Problem 4.1 is not solved, and this phase does not claim a
polynomial CPQR bound on every orthogonal-row matrix.

## Joint third CPQR pivot (2026-10-30)

`milestoneE_joint_cpqr_three_trace` is the third CPQR pivot under the
joint leverage-ratio and coherence hypothesis, plus `3 ≤ k`. The
length-2 prefix still has inverse trace at most
`B = 2 τ^2 n / (k (1 - ρ^2))`. One more pivot adds at most
`(1 + 2 τ^3 / (1 - ρ^2)) · (n - 2) / (k - 2)`. The coefficient
`2 τ^3 / (1 - ρ^2)` is `(τ k / n) / μ`, where
`μ = k (1 - ρ^2) / (2 τ^2 n)` is the length-2 Rayleigh coefficient.
`n` and `k` cancel. The constant was not weakened.

The length-2 card and invertibility come from `cpqrIterate_invariant`.
The trace bound is the length-2 prefix theorem. The third column energy
is at most `τ k / n`: `milestoneE_leverage_sum` gives `n · min ≤ k`, the
leverage hypothesis gives `max ≤ τ · min`, and the Schur residual is
nonnegative, so the quadratic term `q` is at most that energy.
`nextResidual_ge` still supplies the residual floor `(k - 2) / (n - 2)`.

`tests/test_joint_three.py` runs `structselect.cpqr` on the `3×3`
identity. CPQR returns three columns. The Gram inverse trace is `3`.
The formula at `τ = 1`, `ρ = 0`, `k = 3`, `n = 3` equals `5`, and
`3 ≤ 5`. The check does not assert that the trace equals `5`. On that
matrix the inverse trace is `3` and the bound is `5`. The constant is
not claimed sharp. The check is not the theorem.

This does not bound pivots after the third. A 3-column prefix is not a
bound for general `k`. Outcome 3 stays open. Problem 4.1 is not solved,
and CPQR is not claimed to be polynomial on every orthogonal-row matrix.

## Joint CPQR Rayleigh (2026-10-30)

`milestoneE_joint_cpqr_prefix_rayleigh` is the Rayleigh form of the length-2
CPQR prefix under the same hypotheses as
`milestoneE_joint_cpqr_prefix_trace`. For every
`x : Fin (cpqrIterate A 2).card → ℝ`,

```text
k (1 - ρ^2) / (2 τ^2 n) * vecEnergy x ≤
  vecEnergy (selectedCols A (cpqrIterate A 2) *ᵥ x).
```

The coefficient is the reciprocal of the inverse-trace bound
`2 τ^2 n / (k (1 - ρ^2))`. It was not weakened. The argument is the
coordinate identity for a `2×2` symmetric positive-definite matrix: the
numerator of `(a + b) (xᵀ H⁻¹ x) - ‖x‖²` is a sum of squares, so
`‖x‖² ≤ tr(H) · (xᵀ H⁻¹ x)` with `H = G⁻¹`. The Gram diagonal energies
and the positive determinant from `joint_pair_inv_trace` supply
`0 < a`, `0 < b`, and `0 < det`. Then `tr(G⁻¹) ≤ B` gives the stated
coefficient.

`tests/test_joint_rayleigh.py` runs `structselect.cpqr` on the `2×2`
identity. CPQR returns both columns. For `x = (1, 0)`, `‖A_J x‖² = ‖x‖²`.
The coefficient at `τ = 1`, `ρ = 0`, `k = 2`, `n = 2` is `1/2`, and
`1/2 · ‖x‖² ≤ ‖A_J x‖²`. The Rayleigh quotient on that vector is `1`,
because `λ_max ≤ trace`. The bound is not sharp. The check is not the
theorem.

This does not bound later pivots. A length-2 CPQR prefix is not a `k`-set
for `k > 2`. Outcome 3 stays open. Problem 4.1 is not solved, and CPQR is
not claimed to be polynomial on every orthogonal-row matrix.

## Joint CPQR prefix (2026-10-30)

`milestoneE_joint_cpqr_prefix_trace` is the CPQR prefix of length 2 under
the joint leverage-ratio and coherence hypothesis. The hypotheses are
those of `milestoneE_joint_pair_inv_trace`, plus `2 ≤ n`. Empty residuals
sum to `k`, so some column energy is positive and `cpqrPivot` returns a
first column `j0`. After that column, every other column has positive
Schur residual, because the two-column Gram determinant is nonzero and
the selected energy is positive. The second pivot `j1` is therefore
distinct from `j0`, and `cpqrIterate A 2 = {j0, j1}`. The inverse trace
of `selectedColGram A (cpqrIterate A 2)` is at most
`2 τ^2 n / (k (1 - ρ^2))`. The constant was not weakened. `j0` is not
identified with index 0.

`tests/test_joint_cpqr_prefix.py` runs the repository CPQR code on the
`2×2` identity. Both columns are returned, and the inverse trace is `2`,
equal to the formula at `τ = 1`, `ρ = 0`, `k = 2`, `n = 2`. That check
is not the theorem.

This does not bound later pivots. A 2-column CPQR prefix is not a `k`-set
for `k > 2`. Outcome 3 stays open. Problem 4.1 is not solved, and CPQR is
not claimed to be polynomial on every orthogonal-row matrix.

## Joint pair Gram (2026-10-30)

`milestoneE_joint_pair_inv_trace` bounds every two-column Gram of an
orthogonal-row matrix whose leverage ratio is at most `τ ≥ 1` and whose
normalized coherence is at most `ρ` with `0 ≤ ρ < 1`. For `i ≠ j`,
`selectedColGram A {i, j}` is invertible and

```text
((selectedColGram A {i, j})⁻¹).trace ≤ 2 τ^2 n / (k (1 - ρ^2)).
```

Column energies sum to `k`, so some energy is at least `k/n`. The
leverage hypothesis lifts that to a positive floor `(k/n)/τ` on every
energy. Coherence makes the Gram determinant at least
`ℓ_i ℓ_j (1 - ρ^2)`, and the inverse trace of that symmetric `2×2` is
`(ℓ_i + ℓ_j) / det`. The constant was not weakened. On the `2×2`
identity it equals `2`, and on `ℓ = 2/3`, `|c| = 1/3` it equals `4`.
Those checks are in `tests/test_joint_pair.py`. They are not the theorem.

The phase AI census motivated the question. It is not an input to the
proof. The statement does not identify `cpqrIterate A 2`. A bound on
2-column Grams is not a bound on a `k`-set for `k > 2`. Outcome 3 stays
open. Problem 4.1 is not solved, and CPQR is not claimed to be
polynomial on every orthogonal-row matrix.

## Joint leverage-coherence census (2026-10-30)

`experiments/census_joint_seed1.json` is a float census, not a theorem.
The sample uses orthogonal-row frames with `k = 2..8` and `n ≤ 16`.
A frame with measured leverage ratio `L` and normalized coherence `c`
is counted in every cell with `τ ≥ L` and `ρ ≥ c`, for
`τ ∈ {2, 4, 8}` and `ρ ∈ {0.5, 0.7, 0.9}`. Of 428 tried frames, 228
were accepted. Leverage-skew, Kahan-like, near-duplicate, and the Paley
frames in the run missed the loosest cell. The scaled triple-design
frame was not rerun. Its leverages are wildly unbalanced, so the
`19/20` coherence theorem does not put that family in this class, and
it does not exclude the class.

No cell was empty. The recorded maxima of `r_CPQR` are:

| τ | ρ | frames in the cell | max `r_CPQR` | argmax |
| --- | --- | --- | --- | --- |
| 2 | 0.5 | 52 | 0.8164965809277263 | simplex ETF, `3×4` |
| 2 | 0.7 | 85 | 0.866025403784439 | simplex ETF, `2×3` |
| 2 | 0.9 | 100 | 0.866025403784439 | simplex ETF, `2×3` |
| 4 | 0.5 | 56 | 0.8164965809277263 | simplex ETF, `3×4` |
| 4 | 0.7 | 120 | 0.866025403784439 | simplex ETF, `2×3` |
| 4 | 0.9 | 178 | 0.866025403784439 | simplex ETF, `2×3` |
| 8 | 0.5 | 56 | 0.8164965809277263 | simplex ETF, `3×4` |
| 8 | 0.7 | 126 | 0.866025403784439 | simplex ETF, `2×3` |
| 8 | 0.9 | 228 | 0.866025403784439 | simplex ETF, `2×3` |

The largest value in the file is `0.866025403784439`. The `ρ = 0.5`
cells do not contain the `2×3` equiangular frames: their measured
normalized coherence is one unit in the last place above `1/2`, so
those frames sit in the cells with `ρ ≥ 0.7`. Inside every populated
cell, the maximum `r_CPQR` at the values of `k` that occur does not
increase with `k`. For `ρ ≥ 0.7` those per-`k` maxima are
`0.866025403784439`, `0.8164965809277263`, `0.790569415042095`,
`0.7745966692414834`, `0.7637626158259734`, `0.7559289460184545`,
`0.7500000000000001` at `k = 2..8`. For `ρ = 0.5` the same list starts
at `k = 3`. No accepted frame has `r_CPQR > 1`, and none reaches the
named polynomial yardstick.

Hypothesis. No growth was observed, so a later phase may try a positive
theorem on the joint class. The search was finite: `k ≤ 8`, `n ≤ 16`,
and 20 Haar draws at each sampled width. This census does not prove
that theorem. It does not prove the joint class is safe, and it does
not prove the class grows. Outcome 3 stays open. Problem 4.1 is not
solved, and CPQR is not claimed to be polynomial on every orthogonal-row
matrix.

## Bounded coherence is not polynomial (2026-10-30)

`milestoneE_bounded_coherence_no_polynomial` shows that the candidate
class "normalized coherence at most `19/20`" still contains
superpolynomial CPQR frames. For every degree `d` and every `C > 0`,
the scaled triple-design frame at an `m ≥ 20` supplied by
`exists_scale_beats_polynomial` has orthogonal rows, positive column
energy, and normalized coherence at most `19/20`, while its CPQR inverse
energy is strictly above `C (n+k+1)^{2d}`. The constant is the worst
filler ratio at `ε = 45/6400`, namely `83830/88970 < 19/20`; leading
pairs are at most `1/2 + 1/m ≤ 11/20`, and the leading–filler comparison
uses `√14 > 37/10`. The constant `19/20` was not weakened. Any cap
`ρ ≥ 19/20` is too weak, because coherence at most `19/20` implies
coherence at most `ρ`. A stricter cap is not ruled out. This does not
close outcome 1 or outcome 3. Problem 4.1 is not solved, and CPQR is not
claimed to be polynomial on every orthogonal-row matrix.

## Leading–leading coherence (2026-10-30)

`milestoneE_scaled_block_leading_coherence` gives, for every `m ≥ 2` and
all distinct columns of `scaledBlock m = (3 : ℝ) • wideTriangular m`,
`|⟨col i, col j⟩| ≤ (1/2 + 1/m) ‖col i‖ ‖col j‖`. The constant is
`1/2 + 1/m`; it was not weakened. Column `t` of `wideTriangular m` is
supported on rows `l ≤ t`, the inner product of columns `i < j` is
`-wideC m * diag_i ^ 2 + S_i`, and `S_i ≤ wideAlpha m ^ 2 / 4` together
with `diag > wideAlpha m / 2` and `2 * wideC m ≤ 1/m` produce the ratio.
Scaling by `3` multiplies inner products and energies by `9`. This does
not bound filler pairs. A leading–leading ratio `≤ 1/2 + 1/m` is not a
coherence bound on the whole frame. This does not close outcome 3.
Problem 4.1 is not solved, and CPQR is not claimed to be polynomial on
every orthogonal-row matrix.

## Frame coherence for filler pairs (2026-10-30)

`milestoneE_scaled_triple_frame_filler_coherence` gives, for every
`m ≥ 3`, the frame of `milestoneE_scaled_triple_frame` together with
normalized coherence of the filler pairs and of each leading column
against each filler. With `ε = 45 / (16 k)` and `k = m²`, distinct
filler columns `C w_a`, `C w_b` satisfy
`|⟨C w_a, C w_b⟩| ≤ (13/14 + ε)/(1 - ε) · ‖C w_a‖ ‖C w_b‖`, and a leading
column `r_j` against a filler satisfies
`|⟨r_j, C w⟩| ≤ (3(1 + 1/m)/√14 + ε)/√(1 - ε) · ‖r_j‖ ‖C w‖`. The first
bound is the design ratio `13/14` plus the completion inner-product error
`ε`, divided by the contraction `1 - ε`. The second uses the three-point
support of a design column (weights `1, 2, 3`) against the triangular
column, whose diagonal entry dominates the off-diagonal entries by a
factor `m`. Leading–leading pairs are bounded by
`milestoneE_scaled_block_leading_coherence`. No coherence bound on
the whole frame is claimed. This does not close outcome 3. Problem 4.1
is not solved, and CPQR is not claimed to be polynomial on every
orthogonal-row matrix.

## Scaled leading block and the triple-design frame (2026-10-30)

`milestoneE_scaled_triple_frame` gives, for every `m ≥ 3`, the frame
`A = [3 R₀ | C W]` with `R₀ = wideTriangular m`, `C` the symmetric
completion of `3 R₀`, and `W` the triple design reindexed to `k = m²`
rows: `A Aᵀ = I`, CPQR set equal to the leading prefix, image energy `1`,
and inverse energy at least `((2m/3)(4/3)^(m-1))² / 9`. Two inputs made
the triple design usable despite its column energy `1 / (4 (k-1)(k-2))`:
the row-structure bound `‖R₀‖_F² ≤ 5 / (16 k)` (so `‖3 R₀‖_F² ≤ 1` for
`k ≥ 3` and the completion exists), and the contraction `‖C w‖² ≤ ‖w‖²`
(so fillers inherit the design energy without the factor `k` of the
generic completion bound). The scaled threshold is `9 / (16 k²)`, met
for `k ≥ 5`. The filler columns are `C w_a` for pairwise non-parallel
`w_a`, unlike the repeated block of the outcome-2 frame, and the
statement records every completion identity of `C` and design property
of `W`. No coherence bound on the columns of `A` is proved here. This
does not close outcome 3.

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
