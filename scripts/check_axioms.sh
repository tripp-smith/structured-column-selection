#!/usr/bin/env bash
# Fail-closed public-theorem axiom audit. Must terminate; not used by install.
set -euo pipefail
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$(dirname "$0")/.."

lake env lean scripts/AxiomAudit.lean \
  | python3 scripts/check_axiom_output.py \
      scripts/AxiomAudit.lean \
      StructuredColumnSelection/Theorems.lean
