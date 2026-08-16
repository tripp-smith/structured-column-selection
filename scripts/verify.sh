#!/usr/bin/env bash
# Phase-cadence verification. Must terminate; not used by install.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."

echo "verify: lake build"
lake build

echo "verify: sorry scan"
if command -v rg >/dev/null 2>&1; then
  if rg -q sorry --glob '*.lean'; then
    echo "sorry found in Lean sources" >&2
    rg sorry --glob '*.lean' >&2
    exit 1
  fi
else
  if grep -R --include='*.lean' --exclude-dir=.lake -n sorry .; then
    echo "sorry found in Lean sources" >&2
    exit 1
  fi
fi

echo "verify: axiom audit"
python3 - "$PWD" <<'PY'
import pathlib, re, subprocess, sys

root = pathlib.Path(sys.argv[1])
theorems_path = root / "StructuredColumnSelection" / "Theorems.lean"
audit_path = root / "StructuredColumnSelection" / "AxiomAudit.lean"
theorems = re.findall(r"^theorem\s+(milestone[A-Za-z0-9_]+)", theorems_path.read_text(), re.M)
audit_text = audit_path.read_text()
missing = [name for name in theorems if f"StructuredColumnSelection.{name}" not in audit_text]
if missing:
    print("AxiomAudit.lean missing public theorems:", ", ".join(missing), file=sys.stderr)
    sys.exit(1)

proc = subprocess.run(
    ["lake", "env", "lean", "--stdin"],
    input=audit_text.encode(),
    cwd=root,
    capture_output=True,
)
out = proc.stdout.decode() + proc.stderr.decode()
sys.stdout.write(out)
if proc.returncode != 0:
    sys.exit(proc.returncode)

allowed = {"propext", "Classical.choice", "Quot.sound"}
printed = set(re.findall(r"StructuredColumnSelection\.(milestone[A-Za-z0-9_]+)", out))
unprinted = [name for name in theorems if name not in printed]
if unprinted:
    print("axiom audit did not print:", ", ".join(unprinted), file=sys.stderr)
    sys.exit(1)
forbidden = ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler")
for token in forbidden:
    if token in out:
        print(f"unexpected axiom token {token}", file=sys.stderr)
        sys.exit(1)
for match in re.finditer(r"depends on axioms:\s*\[(.*?)\]", out, re.S):
    axioms = {part.strip() for part in match.group(1).replace("\n", " ").split(",") if part.strip()}
    extra = axioms - allowed
    if extra:
        print("unexpected axioms:", ", ".join(sorted(extra)), file=sys.stderr)
        sys.exit(1)
print("axiom audit: public theorems use only propext, Classical.choice, Quot.sound")
PY

echo "verify: pytest"
python3 -m pytest

echo "verify.sh: lake build, no sorry, axiom audit, pytest ok"
