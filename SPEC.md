## 1. Project objective

Simons Workshop Problem 4.1 asks for structural or problem-dependent assumptions on a matrix (A) under which an efficient greedy or randomized column-selection algorithm has quasi-optimal CSSP or RRQR guarantees. The workshop defines CSSP quasi-optimality by

[
|\Pi_JA-A|*{{2,F}}
\le
c(n,k)
\min*{\operatorname{rank}(B)\le k}
|A-B|_{{2,F}},
\tag{7}
]

and RRQR by polynomial control of the singular values of the selected rank-(k) approximation and its residual in equations (8) and (9). For unrestricted CPQR, known worst-case estimates can grow exponentially in (k), despite much better empirical behavior. ([arXiv][1])

This repository will address Problem 4.1 through the structural assumption

[
\boxed{AA^T=I_k,\qquad A\in\mathbb R^{k\times n},\quad k\le n.}
]

Equivalently,

[
A=Q^T,\qquad Q\in\mathbb R^{n\times k},\qquad Q^TQ=I_k.
]

The columns of (A) therefore form a Parseval frame.

The project has two principal tracks:

1. **Randomized track:** formally prove a quasi-optimal rank-revealing column selection theorem for orthogonal-row matrices using size-(k) volume sampling.
2. **Greedy track:** determine whether CPQR has a comparable polynomial guarantee on the same matrix class. Prove such a theorem, disprove it by explicit counterexample, or isolate an additional static structural assumption sufficient to make it true.

The randomized track is the minimum success criterion. The CPQR track is the main open research target.

## 2. Why this structural class

The orthogonal-row case is explicitly identified by the Problem 4.1 working group as an important RRQR specialization, including applications to model reduction and low-rank approximation. The workshop separately asks whether QRCP achieves a bound comparable to the known (\sqrt{k(n-k+1)}) existential result. ([arXiv][1])

It has several advantages for a Lean-first research project.

First,

[
AA^T=I_k
]

removes irrelevant conditioning of the full matrix. All nonzero singular values of (A) equal one. The problem reduces to finding a well-conditioned (k\times k) column submatrix.

Second, column selection can be studied through principal minors of the projector

[
G=A^TA=QQ^T,
\qquad
G^2=G.
]

This gives exact determinant, Schur-complement, leverage-score and volume identities amenable to formal verification.

Third, it creates a clean bridge between a randomized algorithm we can already analyze sharply and CPQR, whose empirical performance is the deeper question.

## 3. Core rank-revealing objective

For (J\subseteq[n]) with (|J|=k), let

[
A_J=A(:,J)\in\mathbb R^{k\times k}.
]

The central quality metric is

[
\kappa_J^{\mathrm{inv}}
:=
|A_J^{-1}|_2
============

\frac{1}{\sigma_{\min}(A_J)}.
]

A small value means that the selected columns form a stable basis for the complete row space.

Since (AA^T=I), every invertible (A_J) gives the exact interpolative representation

[
A=A_JT_J,
\qquad
T_J=A_J^{-1}A,
]

with

[
|T_J|_2
\le
|A_J^{-1}|_2.
]

Thus control of (|A_J^{-1}|_2) is the central RRQR certificate for this structural class.

## 4. Randomized algorithm: volume sampling

For every (J\subseteq[n]) with (|J|=k), define its squared volume

[
w(J)
====

\det(A_J)^2.
]

Since

[
AA^T=I_k,
]

Cauchy-Binet gives

[
\sum_{|J|=k}\det(A_J)^2
=======================

# \det(AA^T)

1.

]

The weights therefore define a probability distribution directly:

[
\boxed{
\Pr(J)=\det(A_J)^2.
}
]

This is size-(k) volume sampling.

Existing volume-sampling theory gives, for a full-rank (X\in\mathbb R^{n\times d}) and a sample of size (s\ge d),

[
\mathbb E\left[(X_S^TX_S)^{-1}\right]
=====================================

\frac{n-d+1}{s-d+1}(X^TX)^{-1}.
]

Efficient reverse-iterative algorithms with (O(nd^2))-scale runtime are known. ([arXiv][2])

Taking

[
X=Q,\qquad d=s=k,\qquad Q^TQ=I
]

gives the project's first headline identity:

[
\boxed{
\mathbb E_J\left[(A_JA_J^T)^{-1}\right]
=======================================

(n-k+1)I_k.
}
]

Consequently,

[
\mathbb E
\operatorname{tr}\left((A_JA_J^T)^{-1}\right)
=============================================

k(n-k+1).
]

Since

[
|A_J^{-1}|_2^2
\le
|A_J^{-1}|_F^2
==============

\operatorname{tr}\left((A_JA_J^T)^{-1}\right),
]

we obtain

[
\boxed{
\mathbb E|A_J^{-1}|_2^2
\le
k(n-k+1).
}
]

Markov then gives, for (0<\delta<1),

[
\boxed{
\Pr\left[
|A_J^{-1}|_2
\le
\sqrt{\frac{k(n-k+1)}{\delta}}
\right]
\ge
1-\delta.
}
]

For constant success probability this has exactly the same asymptotic scale as the workshop's existential

[
\sqrt{k(n-k+1)}
]

bound.

## 5. Headline randomized theorem target

Status annotation (2026-10-24): the unconditional expectation equality below
is refuted on singular-support frames. The all-frame inequality and direct
inverse-energy probability theorem are delivered in the actual-inverse phase;
see the final status correction. The efficient sampler remains open.

The primary public Lean theorem should ultimately have the mathematical content:

> **Theorem R1, randomized rank revelation for orthogonal rows.**
> Let (A\in\mathbb R^{k\times n}) satisfy (AA^T=I_k), and let (J) be a size-(k) subset drawn with probability proportional to (\det(A_J)^2). Then (A_J) is nonsingular almost surely and
>
> [
> \mathbb E|A_J^{-1}|_F^2
> =======================
>
> k(n-k+1).
> ]
>
> Moreover, for every (0<\delta<1),
>
> [
> \Pr\left[
> |A_J^{-1}|_2
> \le
> \sqrt{\frac{k(n-k+1)}{\delta}}
> \right]
> \ge1-\delta.
> ]

The theorem should be expressed using an explicit finite distribution over `Finset (Fin n)` rather than requiring measure-theoretic machinery early in the development.

The implementation should use an efficient reverse-iterative volume sampler rather than enumerate all (\binom nk) subsets.

This result constitutes the repository's concrete answer to Problem 4.1 for the structural class (AA^T=I). It should **not** be described as resolving all of Problem 4.1 or Problem 4.3.

## 6. Exact expectation theorem

Status annotation (2026-10-24): this original inverse identity is false without
extra support assumptions. The proved adjugate identity is distinct. The
original text is retained as a refuted target, not a completed theorem.

A stronger theorem should be formalized before the probabilistic corollary:

[
\boxed{
\sum_{|J|=k}
\det(A_J)^2
(A_JA_J^T)^{-1}
===============

(n-k+1)I_k.
}
]

This finite matrix identity is preferable as the formal core.

The probabilistic expectation statement becomes a thin wrapper around it.

An important design goal is to prove the identity with minimal imported probability theory, ideally through:

1. Cauchy-Binet;
2. determinant/cofactor identities;
3. adjugates;
4. sums of complementary minors.

This should make the proof suitable for eventual extraction into mathlib if the supporting lemmas are general enough.

## 7. Greedy research track: CPQR

Define ordinary column-pivoted QR on

[
A\in\mathbb R^{k\times n}
]

by repeatedly selecting the unchosen column with largest residual norm after projection onto the span of the previously selected columns.

Equivalently, at stage (t), choose

[
j_t
\in
\arg\max_{j\notin J_t}
|(I-\Pi_{J_t})a_j|_2.
]

Run until (k) columns have been selected.

Let (J_{\mathrm{CPQR}}) denote the resulting set.

The primary greedy conjecture is deliberately broad:

[
\boxed{
AA^T=I
\quad\Longrightarrow\quad
|A(:,J_{\mathrm{CPQR}})^{-1}|_2
\le
\operatorname{poly}(n,k).
}
]

The ideal theorem is considerably stronger:

[
|A(:,J_{\mathrm{CPQR}})^{-1}|_2
\le
C\sqrt{k(n-k+1)}
]

for a universal or slowly growing (C).

This is closely aligned with the workshop's Problem 4.3. The workshop notes that classical exponential CPQR bounds remain available, yet the standard worst-case examples do not satisfy the orthogonal-row structure. ([arXiv][1])

No documentation in the repository should initially state the CPQR conjecture as true.

## 8. CPQR discovery phase

Before attempting a general Lean proof, implement an exact and numerical census.

Test:

* (2\le k\le 8), with increasing (n);
* random Haar/Stiefel frames;
* normalized Hadamard and Fourier-type frames;
* random unit-norm tight frames;
* highly nonuniform leverage-score frames;
* nearly duplicated column directions compensated elsewhere to maintain (AA^T=I);
* equiangular or near-equiangular tight frames where available;
* orthogonalized variants of known adverse CPQR constructions.

For each instance compute:

[
r_{\mathrm{CPQR}}
=================

\frac{|A_{J_{\mathrm{CPQR}}}^{-1}|_2}
{\sqrt{k(n-k+1)}}.
]

Compare against:

* optimal exhaustive subset for small (n);
* volume sampling;
* maximum-volume subset;
* a known deterministic (O(nk^2)) selection method;
* strong RRQR.

Record:

[
\sigma_{\min}(A_J),
\quad
|\det A_J|,
\quad
|A_J^{-1}|_2,
\quad
|A_J^{-1}|_F,
]

plus leverage scores and pivot trajectory.

The key research question is whether (r_{\mathrm{CPQR}}) remains bounded or exhibits systematic growth.

## 9. Counterexample protocol

If numerical searches suggest that orthogonal rows alone do not give a polynomial CPQR bound:

1. minimize the dimension;
2. recover a rational or algebraic representation;
3. certify (AA^T=I) exactly;
4. certify every CPQR pivot;
5. certify the final inverse-norm lower bound;
6. formalize the witness in Lean.

The repository should treat a disproof as a first-class research result, just as the current Nyström project treats the (3\times3) SDD counterexample.

A negative result must distinguish:

[
\text{orthogonal rows insufficient}
]

from

[
\text{CPQR insufficient under all reasonable structure}.
]

Only the first would have been shown.

Python automation for steps 2–5 (and Lean snippet emission for step 6)
lives in `structselect.certify`. A `C = 1` certificate is not a
polynomial-bound disproof.

## 10. Conditional structural refinement

If orthogonal rows alone are insufficient, search for the weakest useful additional static condition.

Candidate properties include bounded leverage ratio,

[
\ell_j=|a_j|_2^2,
\qquad
\frac{\max_j\ell_j}{\min_j\ell_j}\le \tau,
]

bounded coherence,

[
\frac{|\langle a_i,a_j\rangle|}
{|a_i|,|a_j|}
\le\rho,
]

or a combination of leverage balance and local Gram control.

The additional assumption must satisfy three criteria:

* it is stated from (A) alone and does not refer to CPQR's eventual pivots;
* it is efficiently checkable or naturally guaranteed by an application class;
* it is materially weaker than assuming every (k)-column subset is already well conditioned.

A theorem proved only under a condition equivalent to the desired conclusion does not count as solving this phase.

## 11. CSSP bridge theorem

A second important contribution should connect the orthogonal-row selection theorem to ordinary approximate-rank matrices.

Let

[
A=B+E,
\qquad
B=U\Sigma Q^T,
]

where

[
U^TU=I,\qquad Q^TQ=I,
]

and (B) has rank (k).

For a selected row set (J) of (Q), define

[
T_J=Q_J^{-T}Q^T.
]

Then

[
B=B(:,J)T_J.
]

Using the actual columns of (A),

[
A-A(:,J)T_J
===========

E-E(:,J)T_J.
]

Hence

[
|\Pi_JA-A|_2
\le
\left(1+|Q_J^{-1}|_2\right)|E|_2,
]

and analogously

[
|\Pi_JA-A|_F
\le
\left(1+|Q_J^{-1}|_2\right)|E|_F.
]

If (B=A_k), the truncated SVD, then

[
E=A-A_k
]

is the optimal rank-(k) residual.

This gives the bridge

[
\boxed{
|\Pi_JA-A|_{{2,F}}
\le
\left(1+|Q_J^{-1}|*2\right)
|A-A_k|*{{2,F}}.
}
]

Combining it with Theorem R1 produces a quasi-optimal CSSP inequality whenever the relevant dominant right-singular frame can itself be efficiently selected or is supplied by the application.

This theorem is valuable even if it is not used as the primary algorithmic result.

## 12. Relation to recent randomized RRQR work

The project must include a literature gate before making novelty claims.

Randomized row/column sampling followed by strong RRQR has already been analyzed for low-rank matrices with incoherence/sparsity structure. ([arXiv][3]) More recent work proves strong rank-revealing properties by applying deterministic sRRQR to random sketches, and a July 2026 revision of SE-QRCS uses sparse embeddings to reduce dimension dependence in column subset selection. ([arXiv][4])

Accordingly, this project should **not** make its principal research claim merely:

> random sketch + sRRQR works.

The distinctive questions are instead:

* exact formal verification of the orthogonal-row volume-sampling theorem;
* comparison with the sharp existential bound;
* whether ordinary CPQR gets a comparable guarantee;
* what minimal additional structure makes CPQR provably quasi-optimal;
* lifting the conditioning result to CSSP perturbation bounds.

## 13. Lean architecture

Suggested modules:

```text
StructuredColumnSelection/
  Definitions.lean
  PrincipalColumns.lean
  OrthogonalRows.lean
  CauchyBinet.lean
  VolumeWeights.lean
  VolumeSampling.lean
  InverseGramExpectation.lean
  RankReveal.lean
  CSSPBridge.lean
  CPQR/
    Definitions.lean
    Residual.lean
    ProjectorGram.lean
    PivotInvariants.lean
    Bounds.lean
  Computable.lean
  SmallInstanceChecks.lean
  Counterexamples/
    CPQR.lean
  Perturbation.lean
  Theorems.lean
  MathlibReady.lean
```

`Definitions.lean` should contain only stable public mathematical concepts.

`VolumeSampling.lean` should use explicit finite weighted sums before introducing general probability abstractions.

`CPQR` should be separated from the randomized proof so failure of the greedy conjecture does not block completion of the core specification.

`Computable.lean` should provide exact rational determinant, volume and CPQR checks for small matrices.

`Theorems.lean` should contain only headline results and re-export them with concise statements.

No public theorem may depend on `sorry`.

## 14. Python application layer

Package name:

```text
structselect
```

Proposed API:

```python
from structselect import (
    volume_sample,
    cpqr_select,
    strong_rrqr_select,
    optimal_subset,
    rrqr_certificate,
    cssp_error,
    leverage_scores,
)
```

Example:

```python
J = volume_sample(A, k, seed=42)

cert = rrqr_certificate(A, J)
print(cert.sigma_min)
print(cert.inverse_norm)

J_cpqr = cpqr_select(A, k)
```

For orthogonal-row matrices the certificate should report:

```text
orthogonal_rows = True
inverse_norm
frobenius_inverse_norm
volume
workshop_scale = sqrt(k * (n-k+1))
ratio_to_workshop_scale
```

The package should distinguish exact exhaustive calculations from floating-point diagnostics.

## 15. Experimental application layer

Create deterministic experiment generators for:

```text
haar_stiefel
hadamard_frame
fourier_frame
balanced_tight_frame
leverage_skew_frame
near_duplicate_frame
random_projector
```

A standard experiment should compare:

```text
CPQR
volume sampling
strong RRQR
optimal exhaustive selection
```

where exhaustive selection is enabled only for small instances.

Produce machine-readable JSON containing the matrix family, dimensions, random seed, selected indices, inverse norm, determinant, smallest singular value and runtime.

Plots and notebooks are optional. The raw experiment pipeline must work without notebooks.

## 16. Formal success criteria

### Milestone A: structural foundations

Lean proves:

[
AA^T=I
\iff
Q^TQ=I
]

under the transpose correspondence, plus the needed identities for selected columns, Gram matrices and determinants.

Status note (Phase 1): implemented in Lean as
`milestoneA_transpose_correspondence`,
`milestoneA_selectedSquare_entry`, and
`milestoneA_selectedGram_formula`.

### Milestone B: volume normalization

Lean proves:

[
\sum_{|J|=k}\det(A_J)^2=1.
]

Status note (Phase 2): implemented in Lean as
`milestoneB_cauchyBinet` and `milestoneB_volume_normalization`,
with independent rational enumerations in
`StructuredColumnSelection/SmallInstanceChecks.lean`.

### Milestone C: exact inverse expectation

Lean proves:

[
\sum_{|J|=k}
\det(A_J)^2
(A_JA_J^T)^{-1}
===============

(n-k+1)I.
]

This is the central formal milestone.

Status note (Phase 3): implemented in Lean as
`milestoneC_adjugate_sum` and
`milestoneC_inverse_gram_expectation`.
The formal summand is `adj(A_J A_Jᵀ)`, which equals
`det(A_J)² (A_J A_Jᵀ)⁻¹` on invertible blocks and retains the
correct singular contribution. Independent rational enumerations are
in `StructuredColumnSelection/SmallInstanceChecks.lean`.

### Milestone D: randomized RRQR guarantee

Lean proves the expectation and high-probability inverse-norm bounds.

At this point the repository has completed its minimum answer to Problem 4.1.

Status note (Phase 4): implemented in Lean as
`milestoneD_expected_inv_frob_sq` and
`milestoneD_markov_inv_frob`. The expectation is
`∑ tr(adj(A_J A_Jᵀ)) = k(n-k+1)`. The tail is a finite Markov bound
on that adjugate-trace proxy for `‖A_J⁻¹‖_F²`, which implies the
spectral bound of Theorem R1 on invertible blocks. Independent
rational enumerations are in
`StructuredColumnSelection/SmallInstanceChecks.lean`.

### Milestone E: CPQR characterization

One of the following must be delivered:

1. a polynomial CPQR theorem for all orthogonal-row matrices;
2. an explicit machine-checked counterexample;
3. a counterexample plus a meaningful stronger structural class with a polynomial CPQR theorem.

Status note (Phase 5 structural CPQR + §8 census + residual energy +
binomial volume): the greedy algorithm is defined in
`ColumnPivotedQR.lean` as `cpqrSet`, with public names
`milestoneE_residual_empty`, `milestoneE_leverage_sum`,
`milestoneE_first_pivot_is_max`, `milestoneE_first_leverage_ge`,
`milestoneE_cpqr_card_le`, `milestoneE_cpqr_card_eq`,
`milestoneE_k1_volume_ge`, `milestoneE_residual_energy`,
`milestoneE_next_residual_ge`, and
`milestoneE_cpqr_volume_ge_binomial`,
`milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`, and
`milestoneE_last_residual_ge`. Orthogonal-row CPQR returns
exactly `k` columns. A first pivot has leverage at least `k/n`. For
`k=1` the selected volume is at least `n⁻¹` (workshop scale).
Independent residuals sum to `k-#J`, and the CPQR volume is at least
`1/C(n,k)`. That binomial factor is exponential in `k` when `n ≈ 2k`
and is not a polynomial inverse-norm bound. The running `2×3` pivot
set is `frame23_cpqr_set`. The Section 8 numerical census lives in
`structselect/census.py` and `experiments/census_seed0.json`. Wave 1
adds ETF / clustered / Haar-growth / block records in
`experiments/census_wave1_*_seed1.json` (worst recorded `r_CPQR`
there is `√3/2` on the `2×3` simplex). Wave 3 proves
a contraction and a last-residual average; those are not a joint
`poly(n,k)` inverse-norm bound. Wave 4 adds
`milestoneE_pivot_gram_inv_trace_le`
(`tr((G')⁻¹) ≤ (n-k+1)(4^k+6k-1)/9`, polynomial in `n` but
exponential in `k`, not a joint `poly(n,k)` bound) and a certified
rational `3×8` witness `frame38` with `r_CPQR > 1`
(`frame38_mul_transpose`, `frame38_cpqr_set`,
`frame38_inv_norm_lb` in `SmallInstanceChecks.lean`,
`native_decide` only). The `frame38` certificate refutes the ideal
`C = 1` bound but stays below the named polynomial
(`4.37 ≪ 512`), so it is not outcome 2; a `4×12` record with
`r_CPQR ≈ 1.236` is numeric only, not certified. Parallel merge
adds `milestoneE_residual_antitone`,
`milestoneE_residual_insert_downdate`,
`milestoneE_gram_inv_trace_eq_sum_inv_residual`,
`milestoneE_sigma_min_ge_inv_sqrt_trace`,
`milestoneE_gsR_mul_transpose` (`R Rᵀ = I`), and
`milestoneE_bidiagonal_U_inv_trace_le` (polynomial inverse-trace
**only if** Gram–Schmidt `U` is bidiagonal: a hypothesis on `U`,
not a class of `A`, not Path 1), and
`milestoneE_k2_inv_trace_le` (`k = 2` only: bidiagonal `U` is
automatic, so `tr((G')⁻¹) ≤ 3(n-1)`; a special case like
`milestoneE_k1_volume_ge`, not Path 1 for general `k`). Path 2 search
(`structselect/adverse.py`,
`experiments/cpqr_adverse_ladder_seed20260816.json`) is
polynomial-looking through `k = 8`; worst recorded `(8,24)` has
inverse norm `≈ 30.98`, `r_CPQR ≈ 2.66` (`≈ 0.17%` of the named
polynomial); `C = 1` witnesses exist; no superpolynomial family.
`structselect/certify.py` re-certifies `frame38`. Path 3 adds
`milestoneE_cpqr_inv_energy_le_choose` (`‖x‖² ≤ k C(n,k) ‖A_J x‖²`,
exponential / not polynomial) and
`milestoneE_cpqr_inv_energy_le_of_minDim` (polynomial inverse
energy on the static class `min(k, n-k) ≤ d`). That class is
checkable from the shape of `A` alone and is weaker than “every
`k`-set is well-conditioned.” It is **not** a joint `poly(n,k)`
theorem for every orthogonal-row matrix.

Status note (explicit adverse family): outcome 2 is delivered by
`milestoneE_wide_adverse_family`,
`milestoneE_cpqr_no_joint_polynomial`, and
`milestoneE_cpqr_named_polynomial_obstruction`. For every `m ≥ 2`
there is an orthogonal-row frame whose CPQR set is the leading
prefix, with image energy `1` and inverse energy at least
`((2m/3)(4/3)^(m-1))²`. For every degree `d` and every `C > 0`,
some actual CPQR block satisfies
`C(n+k+1)^{2d} ‖A_J x‖² < ‖x‖²`. The case `d = 4`, `C = 1` is
`max(n³, k³, (k(n-k+1))²)² ‖A_J x‖² < ‖x‖²`. This is not a
polynomial inverse bound for every orthogonal-row matrix.
Outcomes 1 and 3 remain open.

Status note (CSSP bridge): `milestoneF_cssp_spectral` and
`milestoneF_cssp_frobenius` are the SPEC §11 comparison for a supplied
orthonormal factor `Q`. Both state
`‖A - A_J T‖ ≤ (1 + ‖Q_J⁻¹‖₂) ‖E‖`, with `T = (Q_Jᵀ)⁻¹ Qᵀ`, the left-hand
norm spectral or Frobenius, and the coefficient spectral in both.

Status note (frame coherence, filler pairs):
`milestoneE_scaled_triple_frame_filler_coherence` gives, for every
`m ≥ 3`, the scaled triple-design frame together with filler–filler
normalized coherence at most `(13/14 + ε)/(1 - ε)` and leading–filler
normalized coherence at most `(3(1 + 1/m)/√14 + ε)/√(1 - ε)`, where
`ε = 45 / (16 k)`. No coherence bound on the whole frame is claimed.
This is not a polynomial inverse-norm bound for CPQR. Outcome 3 stays open.

Status note (leading–leading coherence):
`milestoneE_scaled_block_leading_coherence` gives, for every `m ≥ 2` and
all `i ≠ j`, normalized coherence of the corresponding columns of
`scaledBlock m` at most `1/2 + 1/m`. This does not bound filler pairs,
and a leading–leading ratio `≤ 1/2 + 1/m` is not a coherence bound on the
whole frame. This is not a polynomial inverse-norm bound for CPQR.
Outcome 3 stays open.

Status note (scaled triple-design frame):
`milestoneE_scaled_triple_frame` gives, for every `m ≥ 3`, an
orthogonal-row frame `[3 R₀ | C W]` with the triple design `W` and the
symmetric completion `C`: CPQR set equal to the leading prefix, image
energy `1`, inverse energy at least `wideGrowthLower m ^ 2 / 9`, with
`‖3 R₀‖_F² ≤ 45 / (16 k)`. The filler directions are pairwise
non-parallel design columns, but no coherence bound on the frame's
columns is claimed. Outcome 3 stays open.

Status note (weighted signed triple design):
`milestoneE_triple_design` gives, for every `n`, a tight design
`W Wᵀ = 1` in `ℝ^(n+3)` with `4 (n+3)(n+2)(n+1)` columns, equal column
energy `1 / (4 (n+2)(n+1))`, and pairwise normalized inner product at
most `13/14`. The design is an input for the design frame of
`milestoneE_design_adverse_family`; its column energy is above that
theorem's `1 / wideRepeats` cap, so no adverse frame and no coherence
bound on any orthogonal-row frame is claimed. Outcome 3 stays open.

Status note (symmetric completion):
`milestoneE_symmetric_completion` gives every `R` with `‖R‖_F² ≤ 1` a
symmetric completion `R Rᵀ + C Cᵀ = 1` with the inner-product identity
`⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`, the energy sandwich
`(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and the perturbation bound
`‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`. No coherence bound on any frame is
claimed. Outcome 3 stays open.

Status note (design-padded adverse family):
`milestoneE_design_adverse_family` replaces the repeated filler block of
the outcome-2 frame by any tight design `W` with `W Wᵀ = 1` and column
energy at most `1 / wideRepeats m`, with any completion `C`. The frame
`[R | C W]` has orthogonal rows, the CPQR prefix, image energy `1`, and
inverse energy at least `wideGrowthLower m ^ 2`. No coherence bound on
its columns is claimed. Outcome 3 stays open.

Status note (normalized coherence):
`milestoneE_normalized_coherence_one` says that the outcome-2 frame has
two equal positive columns, so their normalized coherence is `1`, and
the CPQR block still beats `C (n + k + 1)^{2d}`. A class that requires
every normalized ratio to be at most some `ρ < 1` excludes this frame.
The theorem does not give a polynomial CPQR bound on a stricter ratio.
Outcome 3 stays open.

Status note (absolute incoherence escape):
`milestoneE_incoherent_no_joint_polynomial` says that for every `ρ > 0`,
`ColumnIncoherent A ρ` contains an orthogonal-row frame whose CPQR block
beats `C (n + k + 1)^{2d}`. The predicate bounds absolute inner products,
not the normalized coherence ratio. Outcome 3 stays open.

Status note (equal-energy third pivot):
`milestoneE_equal_energy_third_pivot_split` gives an orthogonal-row
`3×6` frame with equal column energy on which both rules take columns
`0` and `2`, and the third pivots differ. The CPQR set is `{0, 2, 3}`
and the increment set is `{0, 2, 5}`. Outcome 3 stays open.

Status note (equal-energy block split):
`milestoneE_equal_energy_block_pivot_split` gives an orthogonal-row
`3×6` frame with equal column energy on which a non-orthogonal block
makes max-residual CPQR and the increment pivot take different next
columns. Column `5` is orthogonal to column `0`. This does not say the
CPQR set differs from the increment set. Outcome 3 stays open.

Status note (orthogonal equal-energy block):
`milestoneE_equal_energy_orthogonal_block_same_pivot` says that equal
column energy and a pairwise-orthogonal selected block make the next
CPQR pivot agree with the increment pivot. A one-column block is the
agreement half of the equal-energy second pivot. Outcome 3 stays open.

Status note (leverage-ratio pivot split):
`milestoneE_leverage_ratio_pivot_split` gives an orthogonal-row `2×5`
frame with column energies in `[13/50, 16/25]`, leverage ratio `32/13`,
on which max-residual CPQR and the increment pivot select different
columns. Equal energy still makes the second pivots agree. Outcome 3
stays open.

Status note (equal-energy three-row CPQR):
`milestoneE_equal_energy_cpqr_k3` says that when `k = 3`, equal column
energy makes the full CPQR set obey `5n - 12 + 6/n` in inverse trace and
in inverse energy. This is not a bound for general `k`. Outcome 3 stays open.

Status note (equal-energy three-column trace):
`milestoneE_equal_energy_cpqr_three_trace` says that equal column energy
makes the CPQR three-column inverse trace at most the two-column bound
plus one Rayleigh-controlled step. This bounds only that prefix.
Outcome 3 stays open.

Status note (equal-energy prefix Rayleigh):
`milestoneE_equal_energy_cpqr_prefix_rayleigh` says that equal column energy
makes the two-column CPQR Rayleigh quotient at least
`(k - 1) / (2 (n - 1))`. This bounds only that prefix. Outcome 3 stays open.

Status note (equal-energy second pivot):
`milestoneE_equal_energy_cpqr_prefix_trace` says that equal column energy
makes the second CPQR pivot agree with the increment pivot and bounds
the two-column inverse trace by `2 (n - 1) / (k - 1)`. Later pivots stay
open. Outcome 3 stays open.

Status note (adverse family outside orthogonal columns):
`milestoneE_wide_not_incoherent_zero` says that for every `m ≥ 2` the
outcome-2 frame fails `ColumnIncoherent A 0`. The phase-P bound does
not apply to it. Outcome 3 stays open.

Status note (orthogonal-column CPQR): `milestoneE_incoherent_zero_cpqr_bound`
says that `ColumnIncoherent A 0` makes max-residual CPQR select `k`
columns with inverse trace at most `k (n - k + 1)` and
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. The class is stricter than the
SPEC §10 target. Outcome 3 stays open.

Status note (zero-coefficient pivot): `milestoneE_zero_coeff_same_pivot`
says that a zero coefficient on every positive-residual unused column
makes the increment pivot and max-residual CPQR return the same column.
It is not a polynomial CPQR bound. Outcome 3 stays open.

Status note (pivot split): `milestoneE_increment_set_ne_cpqr` says there
is an orthogonal-row `2×5` matrix with `incrementSet A ≠ cpqrSet A`.
It is not a polynomial CPQR bound. Outcomes 1 and 3 stay open.

Status note (increment set): `milestoneE_increment_set_bound` says the
least-index minimizer of the inverse-trace increment selects `k`
columns with inverse trace at most `k (n - k + 1)` and
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. It is not a CPQR bound. Outcome 3
stays open.

Status note (inverse spectral bound): `milestoneE_minimizing_inv_spectral_le`
says some `k` columns chosen by the increment bound satisfy
`‖x‖² ≤ (1 + k (n - k)) ‖A_J x‖²`. It is not a CPQR bound. Outcome 3
stays open.

Status note (inverse-trace induction): `milestoneE_minimizing_inv_trace_le`
says some `k` columns chosen by the increment bound have inverse trace
at most `k (n - k + 1)`. It is not a CPQR bound. Outcome 3 stays open.

Status note (inverse-trace growth step): `milestoneE_inv_trace_growth_step`
says that a block with inverse trace at most
`t (n - t + 1) / (k - t + 1)` can be extended by one column to inverse
trace at most `(t + 1) (n - t) / (k - t)`. It is not a CPQR bound.
Outcome 3 stays open.

Status note (best-column increment): `milestoneE_best_column_increment_le`
says some unused column has positive residual and inverse-trace increment
at most `((n - t) + trace(G⁻¹) - t) / (k - t)`. It is not a CPQR bound.
Outcome 3 stays open.

Status note (inverse-trace step): `milestoneE_append_inv_trace_increment`
is the one-column Gram inverse-trace update
`(1 + ‖G⁻¹ Bᵀ v‖²) / residual`. It is not a CPQR bound. Outcome 3 stays open.

Status note (wide leverage escape): `milestoneE_wide_leverage_escape`
shows that for every `τ ≥ 0` some outcome-2 frame has column energies
in ratio greater than `τ` and greater than `8 m²`. Outcome 3 stays open.
This is not a polynomial bound on a leverage-ratio class.

Status note (hygiene): `scripts/verify.sh` runs `lake build`,
`scripts/check_lean_hygiene.py`, `scripts/check_axioms.sh`
(`scripts/AxiomAudit.lean`), `scripts/CompletionContract.lean`, and
`pytest`. Computational witnesses stay in `SmallInstanceChecks.lean`.
GitHub Actions (`.github/workflows/verify.yml`) runs the Lean gates and
pytest as separate jobs. `CONTRIBUTING.md` records the search-first
proof workflow. Blueprint sources live in `blueprint/src/` and are
optional to build. The obligation ledger is the table at the top of
`RESEARCH.md`.

### Milestone F: CSSP perturbation bridge

Lean proves

[
|\Pi_JA-A|
\le
(1+|Q_J^{-1}|)|A-A_k|
]

in at least spectral norm, ideally both spectral and Frobenius norms.

## 17. Verification and CI

Every push and PR should run:

```bash
lake build
```

and fail on any Lean source containing `sorry`.

Python CI should run:

```bash
python -m pytest
```

Tests should include:

* Cauchy-Binet normalization against direct enumeration;
* exact small rational volume probabilities;
* empirical inverse-Gram expectation converging to ((n-k+1)I);
* exhaustive optimal subsets for (n\le10);
* CPQR deterministic pivot reproducibility;
* orthogonal-row checks;
* CSSP bridge against direct projections;
* comparison of Python values with Lean-certified examples.

Pin the Lean toolchain and mathlib revision as in the Nyström repository.

## 18. Documentation

The repository should contain:

```text
README.md
SPEC.md
FINDINGS.md
RESEARCH.md
APPLICATION.md
MATHLIB.md
CHECKPOINT.md
autonomous-implementation.md
CONTRIBUTING.md
blueprint/
```

`README.md` should lead with the theorem status, not the research ambition.

`FINDINGS.md` should explain the result for a numerical-linear-algebra reader without Lean experience.

`RESEARCH.md` should separate proved statements, empirical observations, conjectures and failed conjectures.

`APPLICATION.md` should document the Python selector and explicitly distinguish rigorous guarantees from heuristics.

`MATHLIB.md` should identify reusable determinant, volume-sampling and finite-expectation lemmas that could plausibly move upstream.

Status note: `CHECKPOINT.md` is the dated reasoning log and next-work
queue. `autonomous-implementation.md` is the engineering playbook.
Neither is a theorem.

## 19. Claim discipline

Before the randomized theorem is complete, say:

> Investigating Simons Problem 4.1 for orthogonal-row matrices.

After Milestone D:

> Machine-checked randomized quasi-optimal column selection for the orthogonal-row case of Simons Problem 4.1.

Do **not** say:

> Solved Problem 4.1.

Do not say CPQR works under orthogonal rows until that theorem exists.

If CPQR fails, the counterexample should be presented as a result rather than a failed project.

The known volume-sampling mathematics should be attributed to its original sources. The potential new contribution is its formalization and, more importantly, whatever is learned about the CPQR boundary. Efficient reverse-iterative volume sampling and the inverse-Gram expectation identities are established prior work. ([arXiv][2])

## 20. Minimum publishable outcome

The repository is successful even if CPQR remains unresolved if it delivers all of:

[
\Pr(J)=\det(A_J)^2,
]

[
\mathbb E[(A_JA_J^T)^{-1}]
==========================

(n-k+1)I,
]

[
\Pr!\left[
|A_J^{-1}|_2
\le
\sqrt{\frac{k(n-k+1)}{\delta}}
\right]\ge1-\delta,
]

an efficient executable volume sampler, and a Lean proof connecting the selected basis conditioning to a rank-revealing guarantee.

The stronger and much more interesting outcome is a CPQR theorem or a minimal CPQR counterexample on orthogonal-row matrices.

## Recommended first attack

I would **not** start by formalizing CPQR.

Start with the finite volume-sampling identity. It has the same favorable characteristics that made the Nyström project work well: small exact examples, a crisp algebraic theorem, a known expected result to validate against, and a clean path from exact computation to a general theorem.

Once

[
\mathbb E[(A_JA_J^T)^{-1}]
==========================

(n-k+1)I
]

is machine checked, implement CPQR and start the computational census.

That creates a solid theorem-producing repository almost immediately, with the higher-risk open problem isolated as the next research phase rather than making the entire project dependent on an unproved CPQR conjecture.

[1]: https://arxiv.org/html/2602.05394 "Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop"
[2]: https://arxiv.org/abs/1806.01969 "Reverse iterative volume sampling for linear regression"
[3]: https://arxiv.org/abs/2402.13975 "A sublinear-time randomized algorithm for column and row subset selection based on strong rank-revealing QR factorizations"
[4]: https://arxiv.org/abs/2503.18496 "[2503.18496] Randomized strong rank-revealing QR for column subset selection and low-rank matrix approximation"

### Status annotation — 2026-10-23 column-budget phase

Additional structural slice (goals unchanged): public names
`milestoneE_column_budget_S_abs_le_one` and
`milestoneE_column_budget_inv_trace_le` deliver inverse-entry and
k(k+1)(n-k+1)/2 inverse-trace control under `gsUColumnBudget`.
This is an extra hypothesis on U, beyond bidiagonal support; no general
Path 1 result, no new frame counterexample, no closure of E or Problem 4.1.


### Status correction — 2026-10-24 actual inverse audit

The unconditional inverse-expectation equalities in §§4–6, §16 C/D and §20
are false when some k-blocks are singular. The historical target text above
is retained for audit. A=[1,0] has actual volume-weighted inverse trace 1,
whereas k(n-k+1)=2; frame23 gives 3 versus 4. Adjugate equalities do not
establish those original actual-inverse equalities. The valid all-frame
trace result is `milestoneD_actual_expected_inv_trace_le`; equality is
`milestoneD_actual_expected_inv_trace_eq_of_full_support` with its explicit
additional hypothesis. The finite probability contract is delivered via
`milestoneD_singular_volume_mass_zero`,
`milestoneD_actual_inv_trace_good_mass`, and
`milestoneD_actual_inverse_energy_good_mass`. The latter directly quantifies
all selected-column vectors, and therefore expresses inverse-energy RRQR.
`milestoneD_actual_expectation_equality_obstruction` certifies the failed
unconditional equality in Lean using real arithmetic and default axioms.
No matrix Loewner-expectation equality or spectral-norm API theorem is claimed.
The efficient executable sampler, E characterization, and F bridge are open.
The previous assertion of a completed minimum publishable package was premature.

### Status annotation — reverse volume phase (2026-10-24)

SPEC §5/§14/§20 executable reverse sampling is implemented by the public
`structselect.volume_sample` and `python3 -m structselect`, for exact rational
Parseval inputs. This is a hybrid reverse algorithm, not subset enumeration.
Its return is an explicit VolumeSample status/certificate record, with indices
in `.selected`; the proposed convenience API in §14 remains partially open.
The finite all-real kernel law is `milestoneD_reverse_sampler_law`, and its
inverse-energy guarantee is `milestoneD_reverse_inverse_energy_good_mass`.
Deletion normalization and the retained-Gram/solve-score bridge have public
`milestoneB_*` names in Theorems.lean. Python extraction, random-bit correctness,
budget-conditioning and rational bit-complexity are not claimed as Lean theorems.
The earlier unconditional inverse-expectation equality remains false. E, F and
the remaining §14/§15 comparison interfaces are open. Canonical verification and
post-merge evidence are linked from README to the phase PR.

### Status annotation — wide completion and prefix core (2026-10-24)

Additional finite structural results, original goals unchanged:
`milestoneE_wide_completion_orthogonal` embeds a small-Frobenius square block
in an explicit-width Parseval frame; `milestoneE_triangular_prefix_projector`
and `milestoneE_triangular_prefix_residual` identify prefix projectors and
residuals from entry hypotheses; `milestoneE_triangular_prefix_pivots` proves
the actual iterate under strict tail-energy dominance.
`milestoneE_wide_parameter_diagonal_lower` bounds the candidate diagonal.
No all-parameter family, qualifying §9 obstruction, joint-polynomial conclusion,
or §16 E closure is delivered. The compressed Python checks are finite evidence.
Randomized sampling and the CPQR track remain separate; F remains open.
