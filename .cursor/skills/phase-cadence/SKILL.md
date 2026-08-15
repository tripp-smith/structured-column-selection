---
name: phase-cadence
description: >-
  Execute one specification-to-verification phase for this repository:
  specify deliverables, implement Lean/Python artifacts, verify, document,
  and ship via branch + draft PR.
---

# Generic phase cadence

Reusable workflow for delivering one scoped phase from `SPEC.md` without
over-claiming theorem status.

## When to use

- User asks to "execute phase N", "run the phase cadence", or "close a
  SPEC milestone"
- `README.md` / `RESEARCH.md` includes an open thread with named outputs
- A formalization slice has to move from contract to verified code

Do not reopen completed milestones unless the user asks to extend them.

For Milestone E characterization (polynomial bound, counterexample,
or refined class), also follow `.cursor/skills/e-characterization/SKILL.md`
and `.cursor/skills/autonomous-implementation/SKILL.md`.
Do not start Milestone F until E is closed or the user asks for F.

## 1. Specify

Write the contract before implementation.

- Map `SPEC.md` milestone language to exact public theorem identifiers.
- Record explicit non-claims (what this phase does **not** prove).
- Identify files that will change (Lean modules + docs).

Each public theorem should have:

| Field | Content |
| --- | --- |
| Name | Exact Lean identifier |
| Statement | Mathematical claim in repository terminology |
| File | `StructuredColumnSelection/*.lean` target |
| Independent check | Optional rational/finite check if applicable |

Branch from current `main`:

```bash
git checkout -b cursor/<descriptive-name>-e353
```

Use lowercase branch names.

## 2. Implement

- Keep the library target free of `sorry`.
- Prefer exact finite algebra first; defer heavy probability machinery
  until algebraic cores are stable.
- Add or update module exports through `StructuredColumnSelection.lean`
  and `StructuredColumnSelection/Theorems.lean`.
- Put public-facing theorem names in `Theorems.lean`.

## 3. Verify

Run all required checks:

```bash
lake build
rg sorry --glob '*.lean'
```

For structural public theorems, print axioms with `--stdin`
and the fully qualified name:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --stdin <<'LEAN'
import StructuredColumnSelection.Theorems
#print axioms StructuredColumnSelection.<theorem_name>
LEAN
```

Do not use `lake env lean --run` for `#print axioms`.

Allowed defaults: `propext`, `Classical.choice`, `Quot.sound`.

If a closed form is claimed, recompute it independently and keep evidence
in the terminal transcript.

## 4. Document (same logical change as math)

Update phase status and non-claims in:

- `README.md`
- `FINDINGS.md`
- `SPEC.md` (only status annotations, not goal rewrites)
- `RESEARCH.md`
- `APPLICATION.md`
- `MATHLIB.md`

Do not leave stale "open" text for delivered results.

## 5. Ship

One commit per logical change:

```bash
git add <files>
git commit -m "<imperative phase summary>"
git push -u origin cursor/<descriptive-name>-e353
```

Open or update a **draft** PR against `main`.

## Definition of done

- Milestone contract has named theorem outputs
- `lake build` passes
- `rg sorry --glob '*.lean'` is empty
- Public structural theorem axioms are Lean defaults
- Docs reflect delivered vs open work accurately
- Branch is pushed and has a draft PR
