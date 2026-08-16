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

The adjugate form is the correct reading of
`∑ det(A_J)² (A_J A_Jᵀ)⁻¹`. Mathlib's matrix inverse is zero on
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

## What remains open

Milestone E still requires one of: a polynomial CPQR theorem for
general `k`, a machine-checked counterexample past the named
polynomial, or a counterexample plus a stronger static class. The
certified `frame38` witness kills only the ideal `C = 1` bound.
Residual energy, the binomial volume bound, and the triangular trace
bound are proved; the latter two are exponential in `k` and none of
them closes E. The `k = 1` volume bound is a genuine special case
and also does not close E. Milestone F (CSSP bridge) is untouched.
This repository does not claim to have solved all of Problem 4.1.
See `CHECKPOINT.md` for the reasoning log and the next-work queue.
