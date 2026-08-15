---
name: autonomous-implementation
description: >-
  Autonomous specify-implement-verify-document-ship loop for this
  repository. Use when starting a phase, continuing Milestone E, or
  when the user mentions autonomous implementation, cadence, or
  workspace/agent configuration.
---

# Autonomous implementation

This repository is a Lean-first research project. Agents run the loop
below without waiting for a human between specify and ship. Do not
invent theorem status.

## Always-on rules

`.cursor/rules/claim-discipline.mdc` is always applied. Re-read it
when a statement sounds like a bound, a counterexample, or a solution
of Problem 4.1.

## On-demand skills (read the matching file)

| Skill | When |
| --- | --- |
| `phase-cadence` | Any SPEC phase delivery |
| `e-characterization` | Milestone E bound / counterexample / class |
| `verify-public-theorems` | Before shipping, or after Lean edits |
| `claim-discipline` | Any wording about theorems or census |

Do not start Milestone F until E is closed or the user asks for F.

## Single verify command

```bash
export PATH="$HOME/.elan/bin:$PATH"
bash scripts/verify.sh
```

Axioms use `lake env lean --stdin` and fully qualified names. Allowed
defaults: `propext`, `Classical.choice`, `Quot.sound`.

Install (`.cursor/install.sh`) must terminate and must not run tests.
Verify is a separate command.

## Git / PR loop (every turn with edits)

1. Implement on `cursor/<descriptive-name>-e353`.
2. Commit and push the pre-test revision.
3. Open or update the **draft** PR against `main`.
4. Run `scripts/verify.sh` (official test).
5. If anything changes, commit, push, and update the PR again.

## Milestone E protocol

Structural facts (`leverage_sum`, `first_pivot_is_max`, `cpqr_card_eq`)
and the §8 census do **not** close E. Closing E requires one of:

1. a polynomial CPQR inverse-norm theorem for every orthogonal-row matrix;
2. a machine-checked counterexample (SPEC §9);
3. a counterexample plus a stronger static class with a poly theorem.

Useful formal steps that still leave E open:

- residual energy `∑_j residualSq A J j = k - #J` on independent `J`;
- greedy volume `∏` of pivot residuals, hence `volumeWeight ≥ 1 / C(n,k)`;
- the `k = 1` inverse-magnitude bound (workshop scale, not general `k`).

`1 / √C(n,k)` is **not** a polynomial bound in `n` and `k` jointly.
A census with every recorded `r_CPQR < 1` is not a theorem.

## Lean pitfalls

- `open scoped Matrix`, not `open Matrix`, when writing `M i j`.
- `lake env lean --stdin` for `#print axioms`, never `--run`.
- `card_insert_of_notMem` (mathlib v4.33).
- Do not export `native_decide` as a public structural theorem.
