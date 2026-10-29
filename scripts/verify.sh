#!/usr/bin/env bash
# Phase-cadence verification. Must terminate; not used by install.
set -euo pipefail
export PATH="${HOME}/.elan/bin:${PATH}"
cd "$(dirname "$0")/.."

echo "verify: lake build"
lake build

echo "verify: lean hygiene"
python3 scripts/check_lean_hygiene.py

echo "verify: axiom audit"
bash scripts/check_axioms.sh

echo "verify: public expected-type contracts"
lake env lean scripts/CompletionContract.lean

echo "verify: pytest"
python3 -m pytest

echo "verify.sh: lake build, hygiene, axiom audit, contracts, pytest ok"
