"""Frozen experiment inventory and the clean-worktree gate."""

from pathlib import Path

import pytest

from structselect.manifest import check_manifest
from structselect.provenance import require_clean_worktree

ROOT = Path(__file__).resolve().parents[1]


def test_frozen_experiment_inventory_matches_manifest():
    assert check_manifest(ROOT) == []


def test_clean_worktree_returns_revision():
    def runner(args, cwd):
        assert cwd == ROOT
        if args[1] == "status":
            return ""
        assert args[1:] == ["rev-parse", "HEAD"]
        return "abc123\n"

    assert require_clean_worktree(ROOT, runner=runner) == "abc123"


def test_dirty_worktree_refuses_canonical_output():
    def runner(args, cwd):
        assert args[1] == "status"
        return " M structselect/adverse.py\n"

    with pytest.raises(RuntimeError, match="clean worktree"):
        require_clean_worktree(ROOT, runner=runner)
