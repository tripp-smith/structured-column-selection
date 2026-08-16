# Formalization blueprint

Lean blueprint sources for the public theorem graph. Nodes are wired to
declaration names in `StructuredColumnSelection/Theorems.lean`.

This graph is documentation. It does not close Milestone E, and a
missing web build must not block `lake build` or `scripts/verify.sh`.

## Layout

```text
blueprint/src/web.tex       plasTeX / leanblueprint web driver
blueprint/src/print.tex     PDF driver
blueprint/src/content.tex   theorem nodes and `\lean{...}` names
blueprint/src/macros/       shared and format-specific macros
```

## Local build (optional)

Requires [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
and, for the web graph, Graphviz.

```bash
python3 -m pip install leanblueprint
export PATH="$HOME/.elan/bin:$PATH"
lake build
leanblueprint checkdecls   # every `\lean{...}` name must exist
leanblueprint pdf          # needs a TeX engine
leanblueprint web          # needs plasTeX + Graphviz
leanblueprint serve        # local HTTP view of the web build
```

Do not add the web build to CI: it is heavier than the Lean theorems
and needs Graphviz development libraries.

## Nodes

| Node | Lean names | Status |
| --- | --- | --- |
| A–D closed | `milestoneA_*` … `milestoneD_*` | proved |
| E structural | `milestoneE_leverage_sum`, `first_pivot_is_max`, `first_leverage_ge`, `cpqr_card_eq` | proved, not a bound |
| E k=1 | `milestoneE_k1_volume_ge` | proved special case |
| E k=2 | `milestoneE_k2_inv_trace_le` | proved special case |
| E residual / binomial | `milestoneE_residual_energy`, `next_residual_ge`, `cpqr_volume_ge_binomial` | proved, exponential in `k` |
| E triangular | `milestoneE_pivot_gram_inv_trace_le` | proved, poly in `n`, exp in `k` |
| E bidiagonal-U | `milestoneE_bidiagonal_U_inv_trace_le`, `gsR_mul_transpose` | proved hypothesis on `U`, not Path 1 |
| E OPEN | — | SPEC §16 still open for general `k` |
| F OPEN | — | do not start |
