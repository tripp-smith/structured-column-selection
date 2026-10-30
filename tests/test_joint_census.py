"""Joint leverage-coherence census. A ratio above 1 would be an observation."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from structselect.census import max_abs_col_inner, mercedes_benz, normalized_coherence
from structselect.manifest import check_manifest

ROOT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / "experiments" / "census_joint_seed1.json"
GRID = {
    (2.0, 0.5),
    (2.0, 0.7),
    (2.0, 0.9),
    (4.0, 0.5),
    (4.0, 0.7),
    (4.0, 0.9),
    (8.0, 0.5),
    (8.0, 0.7),
    (8.0, 0.9),
}


def test_normalized_coherence_is_a_ratio():
    frame = mercedes_benz()
    coherence = normalized_coherence(frame)
    absolute = max_abs_col_inner(frame)
    assert coherence == pytest.approx(0.5, abs=1e-12)
    assert absolute == pytest.approx(1.0 / 3.0, rel=1e-9)
    assert coherence != pytest.approx(absolute, rel=1e-6)
    zero_column = np.array([[1.0, 0.0], [0.0, 0.0]])
    assert normalized_coherence(zero_column) is None


def test_joint_census_matches_manifest_and_cell_maxima():
    assert check_manifest(ROOT) == []
    data = json.loads(CENSUS.read_text(encoding="utf-8"))
    assert data["closes_milestone_e"] is False
    assert data["evidence"] == "numeric"
    assert data["seed"] == 1
    note = data["note"].lower()
    assert "not a theorem" in note
    assert "milestone e" in note
    records = data["records"]
    assert data["n_accepted"] == len(records)
    assert data["n_tried"] >= len(records)
    assert records
    for rec in records:
        assert rec["leverage_ratio"] <= 8
        assert rec["normalized_coherence"] <= 0.9
        assert rec["aat_err"] < 1e-8
        assert "matrix" not in rec
    cells = data["cells"]
    assert {(cell["tau"], cell["rho"]) for cell in cells} == GRID
    for cell in cells:
        matched = [
            rec
            for rec in records
            if rec["leverage_ratio"] <= cell["tau"]
            and rec["normalized_coherence"] <= cell["rho"]
        ]
        assert cell["n"] == len(matched)
        if not matched:
            assert cell["max_r_cpqr"] is None
            continue
        assert cell["max_r_cpqr"] == max(rec["r_cpqr"] for rec in matched)
        assert cell["max_inv_over_named_poly"] == max(
            rec["inv_over_named_poly"] for rec in matched
        )
        assert cell["any_r_gt_1"] is any(rec["r_cpqr"] > 1 for rec in matched)
