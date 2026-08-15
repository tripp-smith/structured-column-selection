#!/usr/bin/env bash
# Phase verification: Lean build, no-sorry scan, optional pytest.
set -euo pipefail

export PATH="${HOME}/.elan/bin:${PATH}"

lake build
if rg -n --glob '*.lean' '\bsorry\b'; then
  echo "error: sorry found in Lean sources" >&2
  exit 1
fi

if command -v python3 >/dev/null 2>&1; then
  python3 -m pytest
fi
