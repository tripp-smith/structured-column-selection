---
name: verify-public-theorems
description: >-
  Run the repository verification suite: lake build, sorry scan,
  public-theorem axioms, and pytest. Use before shipping a phase or
  when the user asks to verify Lean theorems.
---

# Verify public theorems

```bash
export PATH="$HOME/.elan/bin:$PATH"
bash scripts/verify.sh
```

Or run the pieces:

```bash
lake build
rg sorry --glob '*.lean'
python3 -m pytest
```

Axioms (use `--stdin`, full constant names):

```bash
lake env lean --stdin <<'LEAN'
import StructuredColumnSelection.Theorems
#print axioms StructuredColumnSelection.milestoneE_cpqr_card_eq
LEAN
```

Allowed defaults: `propext`, `Classical.choice`, `Quot.sound`.

Lean pitfalls already learned:

- Do not `open Matrix` if `M i j` then fails; use `open scoped Matrix`
- Avoid `rw` on `M i j` goals; use `Matrix.ext_iff`
- Nat subtraction in a ring: `((n + 1 - k : ℕ) : R)`
- `card_insert_of_notMem` (mathlib v4.33 name)
- Do not export `native_decide` theorems as public structural results
