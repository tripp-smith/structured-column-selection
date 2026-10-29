"""The Lean scan allows computational witnesses in one module only."""

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _load():
    path = ROOT / "scripts" / "check_lean_hygiene.py"
    spec = importlib.util.spec_from_file_location("check_lean_hygiene", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


hygiene = _load()


def test_repository_lean_sources_pass_hygiene():
    assert hygiene.hygiene_errors(ROOT) == []


def test_stray_computational_witness_is_rejected(tmp_path: Path):
    library = tmp_path / "StructuredColumnSelection"
    library.mkdir()
    (library / "Theorems.lean").write_text("theorem foo := by native_decide\n", encoding="utf-8")
    errors = hygiene.hygiene_errors(tmp_path)
    assert any("Theorems.lean" in error for error in errors)


def test_placeholder_is_rejected(tmp_path: Path):
    (tmp_path / "Scratch.lean").write_text("theorem foo : True := by sorry\n", encoding="utf-8")
    errors = hygiene.hygiene_errors(tmp_path)
    assert any("Scratch.lean" in error for error in errors)
