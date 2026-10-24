# Contributing

This is a Lean-first research repository. Search before proving, verify
before claiming, and keep theorem-status language honest.

Canonical sources: `SPEC.md` §16 and §19, `CHECKPOINT.md`,
`.cursor/skills/`, `.cursor/rules/claim-discipline.mdc`.
Do **not** create `AGENTS.md`.

The allowed status line after Milestone D is:

> Machine-checked randomized quasi-optimal column selection for the
> orthogonal-row case of Simons Problem 4.1.

Do not say Problem 4.1 is solved. Do not say CPQR has a joint
`poly(n,k)` inverse-norm bound unless that theorem is proved in
`Theorems.lean`. Census ratios are witnesses, not theorems.

## Verify

```bash
export PATH="$HOME/.elan/bin:$PATH"
bash scripts/verify.sh
```

That runs `lake build`, a `sorry` scan, a public-theorem axiom audit,
and `pytest`. Axiom prints use `lake env lean --stdin`, never `--run`.
Allowed defaults: `propext`, `Classical.choice`, `Quot.sound`.

Install (`.cursor/install.sh`) must terminate and must not run tests
or change git config.

## Search-first proof workflow

Before writing a bespoke proof of a reusable fact:

1. Inspect the exact goal.
2. Search mathlib by theorem or type shape (Loogle, `#check`, `#find`).
   Prefer a shape such as `Matrix.trace (A.reindex e e) = Matrix.trace A`
   over an English phrase such as “trace invariant under permutation”.
3. Try discovery tactics: `exact?`, `apply?`, `simp?`, `aesop?`,
   `grind?`.
4. Look for an existing project abstraction in
   `StructuredColumnSelection/`.
5. Only then write a new lemma, and only after confirming mathlib has
   no suitable result.

When `grind?` / `simp?` propose a proof, replace it with an explicit
lemma list or a readable argument where practical
(`grind only [lemma1, lemma2, ...]`). Do not churn working proofs.
Do not replace a conceptual argument with a huge opaque automation
call merely to shorten it.

Automation conventions: `simp` for canonical rewriting, `norm_num`
for arithmetic, `ring` / `linarith` for identities, `aesop` / `grind`
for search, `native_decide` only for finite decidable certification
in `SmallInstanceChecks.lean`. Public structural theorems must not
depend on `native_decide`.

Lean pitfalls already paid for are in `CHECKPOINT.md` §7. In
particular: `open scoped Matrix`, never `open Matrix`, when writing
`M i j`; do not `rw` on an `M i j` goal; parenthesize `⬝ᵥ` / `*ᵥ`.

## Claim discipline

Before claiming a mathematical result:

1. Name the exact Lean theorem in `Theorems.lean`.
2. Confirm it builds with no `sorry`.
3. Print its axioms.
4. Distinguish a theorem from a finite `native_decide` witness and
   from a numerical census.
5. Update the blueprint node and the status docs
   (`README.md`, `FINDINGS.md`, `SPEC.md` status notes only,
   `RESEARCH.md`, `APPLICATION.md`, `MATHLIB.md`, `CHECKPOINT.md`).

A CPQR counterexample is first-class only after SPEC §9: minimize
dimension, recover an exact matrix, certify `AAᵀ = I`, certify every
pivot, certify the inverse-norm lower bound, then formalize. `r_CPQR > 1`
kills only the ideal `C = 1` bound, not `poly(n,k)`.

Milestone E stays open until one of the three SPEC §16 outcomes lands
for general `k`. Do not start Milestone F unless E is closed or the
user asks. The `k = 1` volume bound and the `k = 2` inverse-trace bound
are special cases, not a Path 1 close.

## Blueprint

Public theorem names are wired in `blueprint/src/content.tex`. See
`blueprint/README.md` for local PDF / web / `checkdecls` commands.
A full leanblueprint web build is optional and is not required for
`scripts/verify.sh`.
