"""Reject proof placeholders and computational witnesses outside their module."""

from __future__ import annotations

import re
import sys
from pathlib import Path

PLACEHOLDER = re.compile(
    r"\bsorry\b|\badmit\b|^\s*(?:private\s+|protected\s+)?axiom\s",
    re.MULTILINE,
)
COMPUTATIONAL = re.compile(r"\bnative_decide\b")
ALLOWED_COMPUTATIONAL = {
    Path("StructuredColumnSelection/SmallInstanceChecks.lean"),
}


def lean_sources(root: Path) -> list[Path]:
    """Return project Lean files, skipping the Lake build directory."""
    files: list[Path] = []
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts or ".git" in path.parts:
            continue
        files.append(path)
    return files


def hygiene_errors(root: Path) -> list[str]:
    """Return one message per forbidden Lean token."""
    errors: list[str] = []
    for path in lean_sources(root):
        text = path.read_text(encoding="utf-8")
        relative = path.relative_to(root)
        if PLACEHOLDER.search(text):
            errors.append(f"proof placeholder or custom axiom: {relative.as_posix()}")
        if COMPUTATIONAL.search(text) and relative not in ALLOWED_COMPUTATIONAL:
            errors.append(
                "computational witness outside SmallInstanceChecks.lean: "
                f"{relative.as_posix()}"
            )
    return errors


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path.cwd()
    errors = hygiene_errors(root)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        raise SystemExit(1)
    print("lean hygiene: no placeholders, custom axioms, or stray computational witnesses")


if __name__ == "__main__":
    main()
