"""Provenance gate for new canonical experiment artifacts."""

from __future__ import annotations

import subprocess
from collections.abc import Callable
from pathlib import Path

GitRunner = Callable[..., str]


def _git(args: list[str], cwd: Path) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True)


def require_clean_worktree(root: Path, runner: GitRunner | None = None) -> str:
    """Return the full HEAD revision, refusing a dirty worktree.

    Call this immediately before writing a new file under ``experiments/``.
    Historical artifacts are not rewritten by this check.
    """
    run = runner or _git
    status = run(["git", "status", "--porcelain"], cwd=root)
    if status.strip():
        raise RuntimeError(
            "canonical experiment output requires a clean worktree; "
            f"git status --porcelain was:\n{status}"
        )
    revision = run(["git", "rev-parse", "HEAD"], cwd=root).strip()
    if not revision:
        raise RuntimeError("canonical experiment output requires a git revision")
    return revision
