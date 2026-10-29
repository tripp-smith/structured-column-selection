"""Fail-closed validation of Lean dependency reports for the public audit list."""

from __future__ import annotations

import re
import sys
from collections import Counter
from collections.abc import Sequence
from pathlib import Path

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
RECORD = re.compile(
    r"'(?P<name>[^'\n]+)' (?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)"
)
PRINT = re.compile(r"^#print axioms (\S+)\s*$", re.MULTILINE)
THEOREM = re.compile(r"^theorem\s+(milestone[A-Za-z0-9_]+)\b", re.MULTILINE)


def declaration_names(audit_source: str) -> list[str]:
    """Return the constants named by `#print axioms` lines, in order."""
    names = PRINT.findall(audit_source)
    if not names:
        raise ValueError("the audit declaration list is empty")
    return names


def public_theorem_names(theorems_source: str) -> list[str]:
    """Return fully qualified public milestone theorems from Theorems.lean."""
    return [
        f"StructuredColumnSelection.{name}" for name in THEOREM.findall(theorems_source)
    ]


def require_audit_covers_theorems(
    audit_names: Sequence[str], theorem_names: Sequence[str]
) -> None:
    """Require the audit list and the public theorem file to name the same constants."""
    if Counter(audit_names) != Counter(theorem_names):
        missing = list((Counter(theorem_names) - Counter(audit_names)).elements())
        extra = list((Counter(audit_names) - Counter(theorem_names)).elements())
        raise ValueError(
            f"audit/theorems mismatch: missing={missing}, extra={extra}"
        )


def validate_axiom_output(output: str, expected: Sequence[str]) -> int:
    """Require every requested declaration and only the permitted axioms."""
    if not expected:
        raise ValueError("the audit declaration list is empty")
    matches = list(RECORD.finditer(output))
    observed = Counter(match.group("name") for match in matches)
    required = Counter(expected)
    if observed != required:
        missing = list((required - observed).elements())
        unexpected = list((observed - required).elements())
        raise ValueError(
            f"declaration coverage mismatch: missing={missing}, extra={unexpected}"
        )
    remainder = RECORD.sub("", output)
    if "depends on axioms" in remainder or "does not depend on any axioms" in remainder:
        raise ValueError("unparsed axiom dependency report")
    for match in matches:
        axioms = {
            value.strip()
            for value in (match.group("axioms") or "").split(",")
            if value.strip()
        }
        disallowed = axioms - ALLOWED_AXIOMS
        if disallowed:
            raise ValueError(
                f"{match.group('name')} uses disallowed axioms: {sorted(disallowed)}"
            )
    return len(matches)


def main() -> None:
    audit_source = Path(sys.argv[1]).read_text(encoding="utf-8")
    theorems_source = Path(sys.argv[2]).read_text(encoding="utf-8")
    output = sys.stdin.read()
    try:
        expected = declaration_names(audit_source)
        require_audit_covers_theorems(expected, public_theorem_names(theorems_source))
        count = validate_axiom_output(output, expected)
    except ValueError as error:
        sys.stdout.write(output)
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
    print(f"Axiom audit passed: {count} declarations; permitted axioms only.")


if __name__ == "__main__":
    main()
