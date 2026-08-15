---
name: claim-discipline
description: >-
  Check or write theorem-status language for this repository. Use when
  updating README/FINDINGS/SPEC/RESEARCH, naming public theorems, or
  deciding whether a CPQR bound or counterexample may be claimed.
---

# Claim discipline

Read `SPEC.md` §19 before writing status text.

Allowed after Milestone D:

> Machine-checked randomized quasi-optimal column selection for the
> orthogonal-row case of Simons Problem 4.1.

Forbidden unless the corresponding Lean theorem exists:

- "solved Problem 4.1"
- "CPQR is polynomial on orthogonal-row matrices"
- treating a census `r_CPQR` as a proved bound

Counterexample protocol (SPEC §9): minimize dimension, recover an
exact representation, certify `AAᵀ = I`, certify every CPQR pivot,
certify the inverse-norm lower bound, then formalize in Lean.

Print axioms of public theorems with:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --stdin <<'LEAN'
import StructuredColumnSelection.Theorems
#print axioms StructuredColumnSelection.milestoneX_name
LEAN
```

Do not use `lake env lean --run` for `#print axioms`.
