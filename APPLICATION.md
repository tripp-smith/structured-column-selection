# Application layer status

Phase 2 adds only an independent volume-weight check, not the full
`structselect` selector API from `SPEC.md`.

`tests/test_volume_normalization.py` enumerates squared maximal minors
for two rational orthogonal-row frames and checks that the weights sum
to `1`. That calculation is a diagnostic witness for Milestone B; the
source of truth is the Lean theorem
`milestoneB_volume_normalization`.

The Python package and experiment pipeline described in `SPEC.md` are
otherwise not implemented. When selectors are added, this document will
separate:

- rigorously certified quantities linked to Lean statements; and
- empirical or heuristic diagnostics used for exploration.
