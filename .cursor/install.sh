#!/usr/bin/env bash
# Idempotent Cloud Agent install script for StructuredColumnSelection.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR/.."

# Install elan (Lean toolchain manager) if missing.
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

# Materialize pinned dependencies and build once to validate setup.
lake exe cache get
lake build
