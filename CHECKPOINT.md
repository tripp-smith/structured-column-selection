# Research checkpoint (2026-08-15)

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
| Milestone E §8 census | **NUMERICALLY OBSERVED** | `structselect/census.py`, `experiments/census_seed0.json` |
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
volumeWeight = 16/25 ≥ 1/2
```

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

### 3.5 Residual-energy / binomial-volume attempt (stalled)

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

The Lean attempt lived briefly in `CPQRVolume.lean` (Schur complement
of `appendColumn` Gram via `Matrix.fromBlocks` + `finSumFinEquiv`).
It stalled on mathlib Matrix notation:

- `open Matrix` makes `M i j` fail; `open scoped Matrix` is required;
- `rw [Matrix.mul_apply]` on a transpose product becomes
  “function expected `(appendColumn B v)ᵀ p.castSucc`”;
- `⬝ᵥ` / `*ᵥ` / `ᵥ*` precedence silently reassociates
  `v ⬝ᵥ G⁻¹ *ᵥ x` as `(v ⬝ᵥ G⁻¹) *ᵥ x`;
- `Write` of `ᵀ` / `⬝ᵥ` near other glyphs corrupted source.

The `k = 1` theorems were extracted and shipped without Schur. The
residual-energy identity is still the right next formal lemma. When
retrying:

1. prove `∑_j a_j ⬝ᵥ (M *ᵥ a_j) = (M * A * Aᵀ).trace` with
   `Matrix.ext_iff` / `simp [mul_apply, transpose_apply]`, never
   `rw` on `M i j`;
2. parenthesize every `⬝ᵥ` / `*ᵥ`;
3. give `fromBlocks` blocks explicit `Matrix _ _ ℝ` ascriptions;
4. mark `selectedProjector` `noncomputable`;
5. compile after each lemma.

Even after it lands, **do not announce a polynomial CPQR theorem.**

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

---

## 4. How Milestone E can close

Exactly one of the following (SPEC §16).

### Path 1 — polynomial theorem for every orthogonal-row matrix

Need `‖A_{J_CPQR}⁻¹‖₂ ≤ poly(n,k)` in Lean, no `sorry`, default
axioms.

Promising formal steps, in order:

1. Residual energy `∑ residual = k − #J` on independent `J`.
2. Each CPQR pivot residual `≥ (k−t)/(n−t)`.
3. Product of residuals `= volumeWeight A (cpqrSet A)`.
4. That gives the binomial bound (exponential; ship it as a
   **non-polynomial** theorem with an explicit non-claim).
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
Killing `poly(n,k)` needs superpolynomial growth or an instance
past every named polynomial.

Constructions that did **not** work after `AAᵀ = I`:

- classical Kahan (orthonormalization kills it);
- leverage-skew and near-duplicate frames in the seed-0 sweep;
- Haar up to `k = 8` in a later probe (worst seen `≈ 0.44`).

Worth trying next, still as Python first:

- Mercedes-Benz / simplex ETF (`k=2, n=3` has `r = √3/2 ≈ 0.866`,
  closer to 1 than Hadamard `2/3`, not a counterexample);
- other ETFs and conference/Paley frames;
- two clusters of near-parallel columns in orthogonal planes,
  *then* row-orthonormalize and check whether the adverse geometry
  survives;
- larger Haar (`k ≥ 10`) only as a growth probe, not a proof.

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

1. **Residual energy in Lean** (`∑ residual = k − #J` on independent
   `J`), then the binomial volume lower bound, labelled as
   exponential / not outcome 1. This is the highest-leverage formal
   step that does not require a new idea.
2. **Deeper census, still Python.** Mercedes-Benz / ETFs; clustered
   near-parallels that survive orthonormalization; larger `k` only
   as a growth probe. Tests must not assert a universal bound. If
   `r_CPQR > 1` appears on a rational matrix, switch to SPEC §9
   immediately and only then add a Lean witness.
3. **`AxiomAudit.lean` + GitHub Actions** reusing `scripts/verify.sh`.
   Cheap, matches playbook Phases 6–7, and prevents silent axiom
   drift.
4. **`CONTRIBUTING.md`** with the search-first proof workflow
   (playbook Phases 3, 4, 14). Do not create `AGENTS.md`.
5. **leanblueprint** (playbook Phase 2) once public theorem names
   are stable. Nodes: A–D, E structural, E `k=1`, E open, F open.
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
| `CPQRVolume.lean` | first leverage and `k = 1` volume |
| `SmallInstanceChecks.lean` | exact `ℚ` witnesses, `native_decide` allowed |
| `structselect/census.py` | §8 generators; witnesses, not theorems |
| `experiments/census_seed0.json` | recorded seed-0 sweep |
| `scripts/verify.sh` | `lake build`, `sorry` scan, pytest |
| `autonomous-implementation.md` | 16-phase engineering playbook |
| `.cursor/skills/autonomous-implementation/SKILL.md` | agent loop |
| `.cursor/skills/e-characterization/SKILL.md` | E protocol |
| `.cursor/rules/claim-discipline.mdc` | always-on claim rules |

---

## 10. Git / PR state at this checkpoint

Merged before this document: PRs #1–#5 (Milestones A–D and the
first E discovery commit on `main`).

Open at writing: PR #6
`cursor/phase-e-cpqr-cadence-e353` — structural E, §8 census,
`k = 1` volume, agent skills. Intended to land on `main` together
with this file.

Branch rule: `cursor/<descriptive-name>-e353`. Draft PR before
official `scripts/verify.sh`; update the PR after any fix.

This run has no linked Cloud Agent environment (`environment: null`).
Do not invent dashboard environment IDs. Install is
`bash .cursor/install.sh` and must not run tests.
