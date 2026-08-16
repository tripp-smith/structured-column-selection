# Research checkpoint (2026-08-16)

This is the working memory for the next agent or human. It records
what was proved, what was only observed, which proof attempts stalled,
and the next concrete moves. It is **not** a theorem.

Status line that remains allowed after Milestone D:

> Machine-checked randomized quasi-optimal column selection for the
> orthogonal-row case of Simons Problem 4.1.

Do **not** say Problem 4.1 is solved. Do **not** say CPQR has a
polynomial inverse-norm bound for general `k`.

Canonical sources: `SPEC.md` §16 and §19, `.cursor/rules/claim-discipline.mdc`.
Engineering playbook: `autonomous-implementation.md` (now on `main`).

---

## 1. Snapshot

| Track | Status | Closing artifact |
| --- | --- | --- |
| Milestone A | **PROVED** | `milestoneA_*` |
| Milestone B | **PROVED** | `milestoneB_cauchyBinet`, `milestoneB_volume_normalization` |
| Milestone C | **PROVED** | `milestoneC_adjugate_sum`, `milestoneC_inverse_gram_expectation` |
| Milestone D | **PROVED** | `milestoneD_expected_inv_frob_sq`, `milestoneD_markov_inv_frob` |
| Milestone E structural CPQR | **PROVED** (not a bound) | `milestoneE_leverage_sum`, `milestoneE_first_pivot_is_max`, `milestoneE_first_leverage_ge`, `milestoneE_cpqr_card_eq` |
| Milestone E, `k = 1` volume | **PROVED** (special case) | `milestoneE_k1_volume_ge` |
| Milestone E residual energy | **PROVED** (not a bound) | `milestoneE_residual_energy`, `milestoneE_next_residual_ge` |
| Milestone E binomial volume | **PROVED** (exponential / not polynomial) | `milestoneE_cpqr_volume_ge_binomial` |
| Milestone E contraction / last residual | **PROVED** (not a joint poly bound) | `milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`, `milestoneE_last_residual_ge` |
| Milestone E triangular trace bound | **PROVED** (poly in `n`, exponential in `k`; not a joint poly bound) | `milestoneE_pivot_gram_inv_trace_le` |
| Milestone E residual monotonicity | **PROVED** (not a bound) | `milestoneE_residual_antitone`, `milestoneE_residual_insert_downdate` |
| Milestone E Gram inverse-trace / `σ_min` | **PROVED** (not a joint poly bound) | `milestoneE_gram_inv_trace_eq_sum_inv_residual`, `milestoneE_sigma_min_ge_inv_sqrt_trace` |
| Milestone E `R Rᵀ = I` | **PROVED** (not a bound) | `milestoneE_gsR_mul_transpose` |
| Milestone E bidiagonal-`U` trace bound | **PROVED** (hypothesis on `U`, not a class of `A`, not Path 1) | `milestoneE_bidiagonal_U_inv_trace_le` |
| Milestone E `C = 1` witness `3×8` | **CERTIFIED** in Lean (kills only `C = 1`; `4.38 ≪ 512` named poly) | `frame38_mul_transpose`, `frame38_cpqr_set`, `frame38_inv_norm_lb` (`SmallInstanceChecks`, `native_decide`) |
| Milestone E `4×12` `r_CPQR > 1` record | **NUMERIC ONLY** (float, not exact-certified) | `experiments/cpqr_r_gt_1_numeric_4_12.json` |
| Milestone E §8 census | **NUMERICALLY OBSERVED** | `structselect/census.py`, `experiments/census_seed0.json` |
| Milestone E Wave 1 census | **NUMERICALLY OBSERVED** | ETF / clustered / Haar-growth / block; `experiments/census_wave1_*_seed1.json` |
| Milestone E Path 2 adverse ladder | **NUMERICALLY OBSERVED** (polynomial-looking through `k=8`; no superpoly family) | `structselect/adverse.py`, `experiments/cpqr_adverse_ladder_seed20260816.json` |
| Milestone E §9 certificate automation | **SHIPPED** (does not close E) | `structselect/certify.py`; re-certifies `frame38` |
| Milestone E characterization | **OPEN** | still needs one of the three SPEC §16 outcomes |
| Milestone F CSSP bridge | **UNTOUCHED** | do not start unless E is closed or the user asks |

Public structural theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`. Verify with `bash scripts/verify.sh`.

Headline Python / Lean witnesses (exact, not numerical):

```text
frame23 = [[1, 0, 0], [0, 3/5, 4/5]]
CPQR selects {0, 2}
‖A_J⁻¹‖₂ = 5/4,   √(k(n-k+1)) = 2,   r_CPQR = 5/8
leverages 1 + 9/25 + 16/25 = 2
first leverage 1 ≥ 2/3

frame12 = [[3/5, 4/5]]
CPQR selects {1}
volumeWeight = 16/25 ≥ 1/2 = 1/C(2,1)

frame23 after {0}: residuals 0 + 9/25 + 16/25 = 1
volumeWeight({0,2}) = 16/25 ≥ 1/3 = 1/C(3,2)

frame38 (rational 3×8, certified in Lean):
CPQR selects {0, 1, 2}
18 ‖A_J x‖² < ‖x‖²  ⇒  ‖A_J⁻¹‖₂ > √18 = √(k(n-k+1)),  r_CPQR > 1 (r_lb ≈ 1.030)
‖A_J⁻¹‖₂ lower bound ≈ 4.37 ≪ 512 = max(n³, k³, (k(n-k+1))²)
```

`frame38` kills only the ideal `C = 1` bound. The `4×12` record
(`r_CPQR ≈ 1.236`) is a float observation, **not** exact-certified.

---

## 2. What Problem 4.1 is, in this repo

Simons Workshop Problem 4.1 asks for structure on `A` that makes an
efficient greedy or randomized column selector quasi-optimal for CSSP
or RRQR. This repository specialises to orthogonal rows

```text
A ∈ ℝ^{k×n},   k ≤ n,   A Aᵀ = I_k
```

(equivalently a Parseval frame). All nonzero singular values of `A`
are 1, so the problem reduces to finding a well-conditioned `k × k`
column block `A_J`. The quality metric is

```text
κ_J^inv := ‖A_J⁻¹‖₂ = 1 / σ_min(A_J)
```

Two tracks:

1. **Randomized (minimum success).** Size-`k` volume sampling
   `Pr(J) = det(A_J)²`. Formalised through Cauchy–Binet, an adjugate
   inverse-Gram identity, and a finite Markov tail. **Delivered
   (Milestones A–D).**
2. **Greedy (open research).** Does ordinary CPQR have a
   `poly(n,k)` inverse-norm bound on the same class? Prove it,
   disprove it, or isolate a stronger static class. **Not closed.**

The ideal greedy theorem is even stronger:

```text
‖A_{J_CPQR}⁻¹‖₂ ≤ C √(k(n-k+1))
```

with `C` universal or slowly growing. `C = 1` is the workshop-scale
dream, not a theorem.

---

## 3. Reasoning log, by phase

### 3.1 Milestones A–D (closed)

These are the randomized track. The design choice that mattered most
was **adjugates instead of mathlib inverses**.

`A⁻¹` in mathlib is `0` on singular blocks. The identity

```text
∑_{|J|=k} det(A_J)² (A_J A_Jᵀ)⁻¹ = (n-k+1) I
```

needs the singular summands. On `frame23` the pair `{1,2}` is
singular and still contributes `adj = [[1,0],[0,0]]`. Dropping it
breaks the sum. So the formal statement is

```text
∑_{|J|=k} adj(A_J A_Jᵀ) = (n-k+1) I     when A Aᵀ = I
```

and more generally `= (n-k+1) adj(A Aᵀ)` without orthogonality.

Proof idea (C): delete one row, apply Cauchy–Binet to the
`(k-1)`-minors, and count that each `(k-1)`-set sits in `n-k+1`
many `k`-sets.

Milestone D is the trace of that identity plus a finitary Markov
inequality on `Finset` sums. No measure-theoretic probability. On
invertible blocks `tr(adj) = det² ‖A_J⁻¹‖_F²`, and
`‖·‖₂ ≤ ‖·‖_F`, so the tail controls the spectral quantity of
Theorem R1 on the invertible locus.

This is the repository's concrete answer to Problem 4.1 for
`AAᵀ = I`. It is not a solution of all of Problem 4.1.

### 3.2 Milestone E, structural layer (proved, not a bound)

Ordinary CPQR is `cpqrSet` in `ColumnPivotedQR.lean`. Residual of
column `j` after set `J` is the Gram-determinant ratio

```text
residualSq A J j = det(B'ᵀ B') / det(Bᵀ B)
```

with `B` the current columns in increasing order and `B'` appending
`j`. Empty `J` is special-cased to column energy `∑_i A_ij²` (the
`Fin 0` vs `Fin #∅` trap). Ties break by smallest index. The
algorithm stops when every unused residual is `≤ 0`.

Proved:

- empty residuals are leverages and sum to `k` (`AAᵀ = I`);
- a first pivot maximises empty residual, hence leverage `≥ k/n`;
- `#(cpqrSet A) ≤ k` always;
- `AAᵀ = I ⇒ #(cpqrSet A) = k`.

The card identity is a rank argument. Residuals are nonnegative
(Gram dets of real matrices). If CPQR stops with `#J < k`, unused
residuals are 0, so unused columns lie in `span(selectedCols)`. Then
`A.rank ≤ #J < k`, contradicting `AAᵀ = I ⇒ A.rank = k`. The
kernel of `appendColumn` is used when residual `= 0` and the current
Gram is invertible.

This is a full-rank stopping theorem, **not** an inverse-norm bound.

### 3.3 Milestone E, `k = 1` (proved special case)

Once first-pivot leverage is `≥ k/n`, the `k = 1` case is immediate:

- `#(cpqrSet A) = 1`, so the set is a singleton `{j}`;
- `volumeWeight A {j} = A_0j² = residualSq A ∅ j`;
- that residual is `≥ 1/n`;
- therefore `|A_0j|⁻¹ ≤ √n = √(k(n-k+1))`.

This **matches the workshop scale** for a single orthonormal row. It
does **not** close Milestone E. SPEC §16 outcome 1 is a polynomial
bound for **all** orthogonal-row matrices, not a slice `k = 1`.
Outcome 3 requires a counterexample *plus* a stronger class; a
special-case theorem without a counterexample is not outcome 3.

### 3.4 SPEC §8 census (NUMERICALLY OBSERVED)

Required precursor. Families: Haar/Stiefel, Hadamard, Fourier,
leverage-skew, near-duplicate, orthogonalized Kahan-like
(`row_orthonormalize` = QR of `Bᵀ`).

Seed-0 sweep (`experiments/census_seed0.json`):

- worst recorded `r_CPQR = 2/3` on Hadamard `k=3, n=8`;
- **no** sample with `r_CPQR > 1`;
- a few Haar draws slightly worse than exhaustive opt, still below
  workshop scale;
- row-orthonormalizing Kahan **destroys** the classical adverse
  structure (`r` stayed small even at `θ = 0.05`, `k = 8`).

Labels, from `autonomous-implementation.md` Phase 8:

| Claim | Label |
| --- | --- |
| `r_CPQR < 1` on the seed-0 sweep | NUMERICALLY OBSERVED |
| `r_CPQR ≤ 1` for all orthogonal-row `A` | CONJECTURED, not even well-posed as a theorem yet |
| CPQR is `poly(n,k)` on this class | CONJECTURED |
| Hadamard `3×8` is a `C = 1` counterexample | false; `2/3 < 1` |
| Kahan is a counterexample after `AAᵀ = I` | DISPROVED as a construction (the orthonormalized matrix is well-behaved) |

A single matrix with `r_CPQR > 1` would counter the **ideal** `C = 1`
workshop-scale bound, **not** `poly(n,k)`. A poly disproof needs a
certified superpolynomial family, or one certified instance that
already exceeds every polynomial the project named (SPEC §9).

Do not treat “every sample had `r < 1`” as evidence of a theorem.

### 3.5 Residual energy and binomial volume (proved, not polynomial)

The natural next identity is

```text
AAᵀ = I,  Gram(J) invertible  ⇒  ∑_j residualSq A J j = k − #J
```

Reason: residual is `‖(I−Π) a_j‖₂²` for the orthogonal projector `Π`
onto the current columns, and `∑_j ‖(I−Π) a_j‖₂² = tr((I−Π) A Aᵀ) =
tr(I−Π) = k − t`. Then the next unused residual is at least
`(k−t)/(n−t)`, so the product of CPQR pivot residuals satisfies

```text
volumeWeight A (cpqrSet A) ≥ ∏_{t=0}^{k-1} (k−t)/(n−t) = 1 / C(n,k)
```

and, because `σ_max(A_J) ≤ ‖A‖₂ = 1`,

```text
σ_min(A_J) ≥ |det A_J| ≥ 1 / √C(n,k)
‖A_J⁻¹‖₂ ≤ √C(n,k)
```

**This would be a theorem for all orthogonal-row matrices, but it is
not polynomial in `n` and `k` jointly.** `C(2k,k) ∼ 4^k / √(πk)`.
For `k = 1` it recovers `√n` (already proved). For `k = 2` it only
gives `r ≤ √n / 2`, which is loose compared with the census.

Shipped in `ResidualEnergy.lean` and `CPQRVolume.lean`. Public names:
`milestoneE_residual_energy`, `milestoneE_next_residual_ge`,
`milestoneE_cpqr_volume_ge_binomial`.

The Schur / `fromBlocks` path compiled after:

- `open scoped Matrix`, never `open Matrix`, if writing `M i j`;
- no `rw` on an `M i j` goal; use `Matrix.ext` / `simp only` / `rfl`;
- parenthesize every `⬝ᵥ` / `*ᵥ`;
- give `fromBlocks` blocks explicit `Matrix _ _ ℝ` ascriptions;
- name `⅟G` as a local `Ginv` matrix before writing entries;
- relate `appendColumn` to `selectedCols (insert j J)` by an
  enumeration equivalence (`appendEnum` / `appendToInsertEquiv`),
  then `det_submatrix_equiv_self`.

**Do not announce a polynomial CPQR theorem.** The binomial bound is
the non-polynomial theorem named in Path 1 step 4.

### 3.6 Literature lead (not a claim)

Gu–Eisenstat strong RRQR gives, for general matrices, a polynomial
control of `σ_min(A_J)` in terms of `σ_min(A)` and a growth factor
`η`. For row-orthonormal `A`, `σ_min(A) = ‖A‖₂ = 1`, so strong RRQR
would be polynomial. Ordinary Householder CPQR is **not** strong
RRQR. Kahan shows exponential growth for unrestricted CPQR, but
Kahan is not row-orthonormal, and orthonormalizing it removed the
bad behaviour in the census.

This is a research lead, not a theorem, and not a novelty claim
(SPEC §12: do not claim “random sketch + sRRQR works”).

### 3.7 Wave 0 consults (INCOMPLETE — research lead only)

Budgeted Claude Opus 5 consult did **not** return a usable reply.

- Claude CLI: `claude --list-models` is not a valid flag on this
  install. `claude --model opus -p` failed with
  `OAuth session expired and could not be refreshed`.
- Cursor Task `claude-opus-5-thinking-high`: launched, then stalled
  / was interrupted (~40 min) with no consult text.
- Recovery (2026-08-15): no leftover `claude` or Task processes to
  kill. Did not retry the hung command in a loop. Did **not** spend
  the Kimi K3 / Fable 5 oracle slot (that slot requires a usable
  Claude reply that still needs a second opinion).
- Wave 3 Claude re-consult was also skipped for the same reason.

The notes below are campaign algebra plus Wave 1 evidence, **not**
a consult theorem and **not** a SPEC §16 outcome.

1. Constructions that keep `AAᵀ = I`. Mercedes-Benz / simplex ETF
   survive and are well-defined Parseval frames. Clustered
   near-parallels in orthogonal planes, then `row_orthonormalize`,
   behave like orthonormalized Kahan: the adverse geometry dies.
   Block-diagonal ETF copies stay well-conditioned (`r` falls as
   more copies are added). Haar `k ≤ 12` showed no growth.
2. Improving `σ_min` past `|det|`, or the volume product past
   `1/C(n,k)`, cannot be done *universally*. The simplex ETF
   saturates both equalities (see §3.8). Path 1 therefore needs an
   argument that forbids that equality case when `C(n,k)` is
   exponential (`n ≈ 2k`), not a better universal volume lemma.
3. A joint `poly(n,k)` theorem is still the better bet than a
   superpolynomial family *on present evidence*: every Wave 1
   sample stayed below `r = 1` and far below the named polynomial
   `max(n³, k³, (k(n-k+1))²)`. A superpolynomial disproof would
   need a family with `n ≈ 2k` that is near volume-saturation
   *and* unbalance `≈ 1`. That family was not found.

Ranked lemma list (still to prove; none of these is claimed):

1. `AAᵀ = I ⇒ A` is a contraction, hence `σ_max(A_J) ≤ 1`.
2. Conditional prefix lemma: if the first `k−1` CPQR columns are
   orthonormal, then `‖A_J⁻¹‖₂` is at most polynomial in `n`
   (last residual `≥ 1/(n-k+1)`). Does **not** close E.
3. Show that when `n ≈ 2k`, the CPQR set is far from the simplex
   equality case (`vol · C(n,k) ≫ 1` or unbalance `≪ 1`).
4. Only then a public `milestoneE_cpqr_inv_le_poly`.

### 3.8 Wave 1 census (NUMERICALLY OBSERVED, 2026-08-15)

Seed 1, revision `e302093`, JSON under `experiments/census_wave1_*`.
Every recorded matrix had `AAᵀ ≈ I` (max entrywise error `< 10⁻¹⁵`).
**No** sample had `r_CPQR > 1`. **No** sample met or exceeded the
named polynomial. Tests do not assert a universal bound.

| Track | Worst `r_CPQR` | Instance | `σ_min` | `|det|` | unbalance | `AAᵀ≈I` |
| --- | --- | --- | --- | --- | --- | --- |
| ETF / Paley | `√3/2 ≈ 0.866` | simplex / Mercedes-Benz `k=2,n=3` | `1/√3` | `1/√3` | `1` | yes |
| Clustered | `≈ 0.323` | `k=4,n=8`, `eps=0.1`, 2 clusters | `0.692` | `0.336` | `0.485` | yes |
| Haar growth | `≈ 0.442` | Haar `k=8,n=12` | `0.358` | `0.173` | `0.485` | yes |
| Block ETF | `≈ 0.516` | block simplex `2+3` | `0.500` | `0.289` | `0.577` | yes |

Simplex family (exact pattern, still a witness):
`‖A_J⁻¹‖₂ = √(k+1)`, workshop scale `√(2k)`,
`r_CPQR = √((k+1)/(2k)) → 1/√2`. Volume
`det² · C(k+1,k) = 1` and unbalance `inv · |det| = 1`.
So `1/C(n,k)` and `σ_min = |det|` are **sharp** on this family.
That does **not** close E: `√(k+1)` is polynomial-scale and
`r < 1`.

Clustered near-parallels after `row_orthonormalize` stayed
well-conditioned, including random-rotated planes. Same class of
failure as orthonormalized Kahan.

Haar `k ∈ {8,10,12}`, `n` up to 24: volume was *loose*
(`det² · C(n,k)` from about 7 to several hundred) and `r`
stayed below `0.45`. Exhaustive opt on `n ≤ 12` did not surface
a growing gap.

Mercedes-Benz / simplex `k=2,n=3` is algebraic (`√3/2`), not a
`C = 1` counterexample, and was not sent through SPEC §9.

Wave 2 branch: every sample bounded → do not certify a
counterexample. Wave 3 shipped contraction and last-residual
lemmas (see §3.9). Milestone E remains **OPEN**.

### 3.9 Wave 3 Path 1 formal (2026-08-15)

Consults: Claude CLI still expired; no Cursor Task retry; Kimi /
Fable unused. Proceeded from campaign algebra and Wave 1 evidence.

Shipped in `PrefixInverse.lean`, public names in `Theorems.lean`:

- `milestoneE_mulVec_energy_le`: `AAᵀ = I ⇒` Euclidean energy of
  `A x` is at most the energy of `x`.
- `milestoneE_col_energy_le`: every column leverage is `≤ 1`.
- `milestoneE_last_residual_ge`: the last CPQR residual is at least
  `1 / (n-k+1)`.

A prefix-orthonormal inverse-Frobenius bound (`#J + 2 / residual`,
hence `O(n)` on that class) was attempted and **not** shipped: the
block-inverse trace argument did not compile in this wave. That
remains the next formal target. None of the shipped lemmas is
`milestoneE_cpqr_inv_le_poly`. Milestone E remains **OPEN**.

### 3.10 Wave 4 triangular trace bound and certified `C = 1` witness (2026-08-15)

Shipped in `TriangularBound.lean`, public name in `Theorems.lean`:

- `milestoneE_pivot_gram_inv_trace_le`: for `AAᵀ = I`, the
  pivot-ordered CPQR Gram matrix `G' = Uᵀ Δ U` satisfies
  `tr((G')⁻¹) ≤ (n - k + 1)(4^k + 6k - 1)/9`. The proof factors the
  pivot Gram via Gram–Schmidt (`|U| ≤ 1` by greedy maximality),
  inverts `U` by the finite Neumann series `S = Σ_{p<k} (1-U)^p`,
  bounds `|S i j| ≤ 2^{j-i-1}` by strong induction
  (Businger–Golub), and assembles the trace with the residual-energy
  ratio `1/δ_l ≤ (n-l)/(k-l) ≤ n-k+1`. **Polynomial in `n` but
  exponential in `k`** (`≈ n · 4^k / 9`). This is the Drmač–Gugercin /
  Gu–Eisenstat style estimate; it is NOT a joint `poly(n,k)` bound
  and does NOT close E. Axioms: `propext`, `Classical.choice`,
  `Quot.sound` only.

Certified witness in `SmallInstanceChecks.lean` (`native_decide`,
kept out of `Theorems.lean`):

- `frame38`: rational `3×8` orthogonal-row matrix from an SLSQP
  adverse search, re-parametrized over `ℚ` via a Cayley transform
  (denominator `10⁴`). Certified facts: `frame38 * frame38ᵀ = 1`
  (`frame38_mul_transpose`), CPQR selects `{0,1,2}` with strictly
  positive pivot margins (`frame38_cpqr_set`), and the explicit
  rational test vector gives `18‖A_J x‖² < ‖x‖²`
  (`frame38_inv_norm_lb`), i.e. `‖A_J⁻¹‖₂ > √(k(n-k+1))` and
  `r_CPQR ≥ r_lb ≈ 1.030 > 1`. Independent exact re-certification in
  `tests/test_cpqr_r_gt_1.py` over `Fraction`. Record:
  `experiments/cpqr_r_gt_1_witness_3_8.json`.
- This is a SPEC §9 certification of the `C = 1` case **only**: the
  certified inverse norm `≈ 4.37` is far below the campaign's named
  polynomial `max(n³, k³, (k(n-k+1))²) = 512`, so it is not outcome
  2 of SPEC §16. Milestone E remains **OPEN**.
- `experiments/cpqr_r_gt_1_numeric_4_12.json` records a `4×12` float
  matrix with `r_CPQR ≈ 1.236` (`σ_min ≈ 0.1348`, `AAᵀ` error
  `≈ 2·10⁻¹⁶`). **NUMERIC ONLY**: not exact, not certified in Lean.
  It is a target for future rational certification, not a theorem.

Consults: none (all oracle CLIs unavailable/failed); done directly.

### 3.11 Parallel Milestone E merge (2026-08-16)

Five isolated branches from `8562578` were merged. Public wrappers
in `Theorems.lean` export only honest statements; each docstring
says it does **not** close E. ResidualMono is the residual source
of truth (no duplicate residual modules from tracks B/C).

Proved, default axioms only:

- `milestoneE_residual_antitone`,
  `milestoneE_residual_insert_downdate`;
- `milestoneE_gram_inv_trace_eq_sum_inv_residual`,
  `milestoneE_sigma_min_ge_inv_sqrt_trace`;
- `milestoneE_gsR_mul_transpose` (`R Rᵀ = I`);
- `milestoneE_bidiagonal_U_inv_trace_le`: polynomial inverse-trace
  **only if** Gram–Schmidt `U` is bidiagonal. Hypothesis on `U`,
  not a class of `A`, not Path 1. **Not** a joint `poly(n,k)`
  theorem. Do not export `pivotGram_inv_trace_le_of_bidiagonal` as
  one.

Numeric Path 2 ladder (`structselect/adverse.py`, seed
`20260816`): polynomial-looking through `k = 8`. Worst recorded
`(k,n)=(8,24)` has inverse norm `≈ 30.98`, `r_CPQR ≈ 2.66`
(`inv / named_poly ≈ 0.0017`). `C = 1` witnesses exist. No
superpolynomial family. `structselect/certify.py` re-certifies
`frame38`. Tests do not assert a universal `r_CPQR` bound.

None of the five tracks proved a joint `poly(n,k)` inverse-norm
bound. Milestone E remains **OPEN**. Milestone F untouched.

---

## 4. How Milestone E can close

Exactly one of the following (SPEC §16).

### Path 1 — polynomial theorem for every orthogonal-row matrix

Need `‖A_{J_CPQR}⁻¹‖₂ ≤ poly(n,k)` in Lean, no `sorry`, default
axioms.

Promising formal steps, in order:

1. Residual energy `∑ residual = k − #J` on independent `J`. **Done.**
2. Each CPQR pivot residual `≥ (k−t)/(n−t)`. **Done.**
3. Product of residuals `= volumeWeight A (cpqrSet A)`. **Done.**
4. Binomial bound (exponential; shipped as a **non-polynomial**
   theorem with an explicit non-claim). **Done.**
5. Improve the analysis: `σ_min ≥ |det| / σ_max^{k−1}` is the
   pessimistic step. A polynomial bound needs to stop one singular
   value from eating the whole volume, or show residuals cannot
   unbalance that badly. Census suggests they do not.

Do not start this Lean bound before the census (already done).

### Path 2 — machine-checked counterexample

SPEC §9 protocol, in order:

1. Minimize dimension.
2. Recover a rational or algebraic matrix.
3. Certify `AAᵀ = I` exactly.
4. Certify every CPQR pivot.
5. Certify the inverse-norm lower bound.
6. Formalize in Lean (`SmallInstanceChecks` / a
   `Counterexamples/` module). `native_decide` is allowed for the
   witness, **not** as a public structural theorem.

`r_CPQR > 1` on one matrix kills only the ideal `C = 1` bound.
**Done (Wave 4):** `frame38` (`3×8`, rational) is certified in Lean
with `r_CPQR > 1`; see §3.10. Killing `poly(n,k)` still needs
superpolynomial growth or an instance past every named polynomial.

Constructions that did **not** work after `AAᵀ = I`:

- classical Kahan (orthonormalization kills it);
- leverage-skew and near-duplicate frames in the seed-0 sweep;
- Haar up to `k = 12` in Wave 1 (worst seen `≈ 0.44` at `k=8,n=12`);
- clustered near-parallels in orthogonal planes, then
  `row_orthonormalize` (worst `r ≈ 0.32`; geometry dies);
- Mercedes-Benz / simplex / Paley / icosahedral ETFs (`r ≤ √3/2`);
- block-diagonal ETF copies (`r` falls as copies are added).

Worth trying next, still as Python first:

- frames with `n ≈ 2k` that are near *both* volume-saturation
  (`det² · C(n,k) ≈ 1`) *and* unbalance `≈ 1` (the simplex does
  this only for `n = k+1`, where `C(n,k)` is linear);
- other combinatorial ETFs / Steiner systems with `n ≫ k+1`;
- larger Haar only as a growth probe, not a proof.

### Path 3 — counterexample plus a stronger static class

Only after a counterexample exists. Candidate extra hypotheses
(SPEC §10), all static and checkable from `A` alone:

- bounded leverage ratio `max ℓ_j / min ℓ_j ≤ τ`;
- bounded coherence `|⟨a_i,a_j⟩| / (‖a_i‖ ‖a_j‖) ≤ ρ`;
- leverage balance plus local Gram control.

The extra assumption must be weaker than “every `k`-set is already
well conditioned.” A theorem whose hypothesis is the conclusion
does not count.

---

## 5. Milestone F (leave it)

SPEC §11 / §16: if `A = B + E` with `B` rank `k` and `Q` the right
singular frame of `B`, then

```text
‖Π_J A − A‖ ≤ (1 + ‖Q_J⁻¹‖) ‖A − A_k‖
```

in spectral (ideally also Frobenius) norm. Valuable even if unused
as the primary algorithm. **Do not start F until E is closed or the
user asks for F.**

---

## 6. `autonomous-implementation.md` — what is done vs next

The file on `main` is a 16-phase engineering playbook. Earlier
agents approximated pieces of it with Cursor skills because the
file was not in the workspace yet. Gap list for the next
infrastructure pass:

| Phase | Intent | Current state | Next move |
| --- | --- | --- | --- |
| 1 Audit | read the tree | this checkpoint | keep `CHECKPOINT.md` current |
| 2 Blueprint | leanblueprint graph | **missing** | add `blueprint/` wired to public theorem names |
| 3 Proof discovery | search mathlib first | partial, in skills | add `CONTRIBUTING.md` (do **not** create `AGENTS.md`; env-setup forbids inventing it) |
| 4 Automation | `grind?` / `simp?` then explicit | not standardised | document; do not churn working proofs |
| 5 API | one abstraction above the theorem | mixed | residual energy should be stated for general Gram projectors, not only CPQR |
| 6 CI | more than `lake build` | `scripts/verify.sh` exists; no GitHub Actions on PR #6 | add `.github/workflows` with build / `sorry` / pytest / axiom audit |
| 7 Axiom audit | `#print axioms` in-tree | manual `--stdin` | add `AxiomAudit.lean` and invoke it from `verify.sh` |
| 8 Computational loop | float → exact → Lean | census + `SmallInstanceChecks` | label every RESEARCH claim with the five statuses |
| 9 Property tests | seeded random identities | some Haar loops | add permutation/sign invariance and residual-vs-norm checks |
| 10 Exact checkers | `ℚ` / `native_decide` | `frame12` / `frame23` | keep `native_decide` out of `Theorems.lean` |
| 11 Mathlib-readiness | classify lemmas | `MATHLIB.md` started | refresh after residual energy |
| 12 Maturity docs | README status table | README leads with the allowed status line | add a compact table; do not overclaim |
| 13 Organisation | roles of docs | this file added | keep roles; do not reshuffle |
| 14 Agent rules | search-first Lean | `.cursor/skills/*`, claim-discipline | fold playbook Phase 14 into `CONTRIBUTING.md` and skills |
| 15 No custom tactics | prefer lemmas | followed | keep |
| 16 Final verify | `scripts/verify.sh` | exists; no `lake lint` / blueprint check | extend the script when those tools exist |

Do not weaken theorems to make any of this easier.

---

## 7. Lean pitfalls already paid for

- `open scoped Matrix`, never `open Matrix`, if you write `M i j`.
- Do not `rw` on an `M i j` goal; use `Matrix.ext_iff` / `Eq.trans`.
- Nat subtraction in a ring: `((n + 1 - k : ℕ) : R)`.
- `Finset.min` is `WithTop`; use `min'` after a nonempty check.
- mathlib v4.33: `card_insert_of_notMem` (not `card_insert_of_not_mem`).
- Do not `cases` on `J.card` (it changes `Fin J.card`); use
  `if h0 : J.card = 0`.
- `rank_of_det_ne_zero` returns `Fintype.card`, not `#J+1`; rewrite
  with `Fintype.card_fin`.
- `{j}.card` is not defeq `1`; avoid `det_fin_one` on singleton Grams
  unless you have a card proof in hand.
- `Fin.pos_iff_nonempty.mp` (not `.mpr`) for `0 < card → Nonempty`.
- Parenthesize `-((c)⁻¹ • (B *ᵥ …))`; watch `*ᵥ` vs `•`.
- `#print axioms` via `lake env lean --stdin` and fully qualified
  names (`StructuredColumnSelection.milestoneE_k1_volume_ge`).
  Do **not** use `--run`.
- Keep `native_decide` witnesses in `SmallInstanceChecks.lean` only.
- PATH: `export PATH="$HOME/.elan/bin:$PATH"`.

---

## 8. Suggested next work (priority order)

Work the first item that is still open. Do not start F.

1. **Beat the `4^k` in the triangular trace bound, or a
   non-universal Path 1 argument.** `R Rᵀ = I` is now proved
   (`milestoneE_gsR_mul_transpose`). A polynomial inverse-trace
   bound holds only under a bidiagonal hypothesis on `U`
   (`milestoneE_bidiagonal_U_inv_trace_le`); that is not a class of
   `A` and is not Path 1. The Businger–Golub entry bound
   `|S i j| ≤ 2^{j-i-1}` is sharp for worst-case triangular
   matrices, so closing Path 1 still needs an argument that CPQR's
   greedy pivoting forbids the worst-case `U`. Do not announce a
   polynomial theorem until the joint statement is proved.
2. **Certify a Path 2 instance past the named polynomial, or a
   superpolynomial family (SPEC §9).** The `C = 1` case is certified
   on `frame38`. Path 2 search through `k = 8` is polynomial-looking
   (worst `(8,24)` inverse `≈ 30.98`, `≈ 0.17%` of the named
   polynomial). The `4×12` numeric record remains a certification
   target; Cayley rounding so far drops below `r = 1`. A Path 2
   close needs a certified family growing past every named
   polynomial.
3. **`AxiomAudit.lean` + GitHub Actions** reusing `scripts/verify.sh`.
   Cheap, matches playbook Phases 6–7, and prevents silent axiom
   drift.
4. **`CONTRIBUTING.md`** with the search-first proof workflow
   (playbook Phases 3, 4, 14). Do not create `AGENTS.md`.
5. **leanblueprint** (playbook Phase 2) once public theorem names
   are stable. Nodes: A–D, E structural, E `k=1`, E residual /
   binomial, E open, F open.
6. **Only if a counterexample exists:** isolate the weakest static
   extra hypothesis (leverage ratio / coherence) and prove a poly
   bound on that class.
7. **Milestone F** after E is closed, or if the user asks.

---

## 9. File map

| Path | Role |
| --- | --- |
| `SPEC.md` | mathematical contract; edit status notes only |
| `Theorems.lean` | public names only |
| `ColumnPivotedQR.lean` | CPQR definition and structural proofs |
| `ResidualEnergy.lean` | residual energy and next-residual average |
| `CPQRVolume.lean` | first leverage, `k = 1` volume, binomial volume |
| `PrefixInverse.lean` | contraction, column energy `≤ 1`, last residual |
| `TriangularBound.lean` | pivot-Gram inverse-trace bound (poly in `n`, exp in `k`) |
| `ResidualMono.lean` | residual antitone / rank-1 downdate (source of truth) |
| `SigmaMinBounds.lean` | Gram inverse-trace = sum inv LOO residual; `σ_min ≥ 1/√tr` |
| `RowOrthoConstraints.lean` | `R Rᵀ = I`; poly bound only under bidiagonal `U` |
| `SmallInstanceChecks.lean` | exact `ℚ` witnesses, `native_decide` allowed |
| `structselect/census.py` | §8 generators; witnesses, not theorems |
| `structselect/certify.py` | §9 Cayley/Givens rational certificates; does not close E |
| `structselect/adverse.py` | Path 2 trapezoidal search; witnesses, not theorems |
| `experiments/census_seed0.json` | recorded seed-0 sweep |
| `experiments/census_wave1_*_seed1.json` | Wave 1 ETF / clustered / growth / block |
| `experiments/cpqr_adverse_ladder_seed20260816.json` | Path 2 ladder through `k=8` |
| `scripts/verify.sh` | `lake build`, `sorry` scan, pytest |
| `autonomous-implementation.md` | 16-phase engineering playbook |
| `.cursor/skills/autonomous-implementation/SKILL.md` | agent loop |
| `.cursor/skills/e-characterization/SKILL.md` | E protocol |
| `.cursor/rules/claim-discipline.mdc` | always-on claim rules |

---

## 10. Git / PR state at this checkpoint

Merged before this document: PRs #1–#5 (Milestones A–D and the
first E discovery commit on `main`).

Merged before this residual-energy phase: PRs #1–#6 (Milestones A–D,
structural E, §8 census, `k = 1` volume).

Residual-energy phase: `cursor/phase-e-residual-energy-e353` /
draft PR #7 — residual energy, next-residual average, binomial
volume (exponential / not polynomial).

This Close-E wave: `cursor/phase-e-close-e353` / draft PR #8 —
Wave 1 census, Wave 3 contraction / last-residual, Wave 4
triangular trace bound and certified `C = 1` witness.

Parallel merge (this checkpoint): `cursor/phase-e-parallel-merge-e353`
integrates tracks A–E (residual mono, sigma-min, row-ortho, Path 2
ladder, rational certify) onto that campaign and updates PR #8.
`R Rᵀ = I` proved. Poly bound only under bidiagonal `U`. Path 2
search polynomial-looking through `k = 8`. No joint `poly(n,k)`
theorem. Milestone E remains **OPEN**. Do not start F.

PRs #9 (`cursor/phase-e-rational-certify-e353`) and #10
(`cursor/row-ortho-constraints-e353`) are absorbed by this merge.

Branch rule: `cursor/<descriptive-name>-e353`. Draft PR before
official `scripts/verify.sh`; update the PR after any fix.

This run has no linked Cloud Agent environment (`environment: null`).
Do not invent dashboard environment IDs. Install is
`bash .cursor/install.sh` and must not run tests.
