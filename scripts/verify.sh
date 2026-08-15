#!/usr/bin/env bash
# Phase-cadence verification. Must terminate; not used by install.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."

lake build
if rg -q sorry --glob '*.lean'; then
  echo "sorry found in Lean sources" >&2
  rg sorry --glob '*.lean' >&2
  exit 1
fi
python3 -m pytest
echo "verify.sh: lake build, no sorry, pytest ok"
