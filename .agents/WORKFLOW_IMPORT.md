# Workflow provenance and CSSP bindings

Copied all skills from tripp-smith/gecp-kernel-structure at
`af8b592ca227625aec05e260dbc290bba0261fa2` verbatim. The workflow source is
preserved at `.github/workflows/reference/gecp-ci.yml.source`; its active
CSSP counterpart is `.github/workflows/verify.yml`. Do not run GECP-only
completion contracts or use its package names here.

Bindings when composing these skills with the local phase cadence:
- GECPKernelStructure → StructuredColumnSelection.
- scripts/AxiomAudit.lean and scripts/check_axioms.sh →
  StructuredColumnSelection/AxiomAudit.lean and scripts/verify.sh.
- Python kernelgecp / uv checks → structselect / python3 -m pytest.
- Branch prefix codex/ supersedes the older cursor/ convention.
- A phase is locally checked after root verification; `verified` requires
  final revision CI as specified by the imported cadence.

Keep the original SPEC goals and local claim discipline. The imported
skills are process guidance, not mathematical evidence.
