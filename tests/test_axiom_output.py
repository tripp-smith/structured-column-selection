"""Fail-closed checks for the public axiom-audit parser."""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


def _load():
    path = ROOT / "scripts" / "check_axiom_output.py"
    spec = importlib.util.spec_from_file_location("check_axiom_output", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


audit = _load()


def test_audit_file_covers_every_public_theorem():
    names = audit.declaration_names(
        (ROOT / "scripts" / "AxiomAudit.lean").read_text(encoding="utf-8")
    )
    theorems = audit.public_theorem_names(
        (ROOT / "StructuredColumnSelection" / "Theorems.lean").read_text(encoding="utf-8")
    )
    audit.require_audit_covers_theorems(names, theorems)


def test_parser_accepts_exact_coverage():
    output = (
        "'StructuredColumnSelection.milestoneA_transpose_correspondence' "
        "depends on axioms: [propext, Classical.choice, Quot.sound]\n"
    )
    assert audit.validate_axiom_output(
        output, ["StructuredColumnSelection.milestoneA_transpose_correspondence"]
    ) == 1


def test_parser_rejects_missing_declaration():
    with pytest.raises(ValueError, match="missing"):
        audit.validate_axiom_output(
            "", ["StructuredColumnSelection.milestoneA_transpose_correspondence"]
        )


def test_parser_rejects_disallowed_axiom():
    output = (
        "'StructuredColumnSelection.milestoneA_transpose_correspondence' "
        "depends on axioms: [propext, sorryAx]\n"
    )
    with pytest.raises(ValueError, match="disallowed"):
        audit.validate_axiom_output(
            output, ["StructuredColumnSelection.milestoneA_transpose_correspondence"]
        )


def test_parser_rejects_unparsed_report():
    output = (
        "'StructuredColumnSelection.milestoneA_transpose_correspondence' "
        "depends on axioms: [propext]\n"
        "leftover depends on axioms: [Quot.sound]\n"
    )
    with pytest.raises(ValueError, match="unparsed"):
        audit.validate_axiom_output(
            output, ["StructuredColumnSelection.milestoneA_transpose_correspondence"]
        )


def test_parser_rejects_empty_audit_list():
    with pytest.raises(ValueError, match="empty"):
        audit.validate_axiom_output("nothing\n", [])


def test_audit_mismatch_names_the_gap():
    with pytest.raises(ValueError, match="missing"):
        audit.require_audit_covers_theorems(
            ["StructuredColumnSelection.milestoneA_transpose_correspondence"],
            [
                "StructuredColumnSelection.milestoneA_transpose_correspondence",
                "StructuredColumnSelection.milestoneB_cauchyBinet",
            ],
        )
