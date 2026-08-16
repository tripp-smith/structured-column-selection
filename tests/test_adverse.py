"""Path 2 trapezoidal adverse search: run the search, do not assert a bound.

These tests check that the parametrization is row-orthonormal, that a
small SLSQP search returns well-formed records, and that the committed
JSON (when present) carries seed, revision, and named-poly flags.
They never assert ``r_cpqr < 1`` universally. Census ratios are
witnesses, not theorems. Milestone E stays OPEN.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

from structselect.adverse import (
    DEFAULT_SEED,
    all_tied_fill,
    all_tied_params,
    diagnose_growth,
    nparams,
    pad_kn,
    payload_from_records,
    pivot_margins,
    record_instance,
    run_ladder,
    search_pair,
    slsqp_step,
    trap_from_params,
)
from structselect.census import named_poly_scale

ROOT = Path(__file__).resolve().parent.parent
JSON_PATH = ROOT / "experiments" / f"cpqr_adverse_ladder_seed{DEFAULT_SEED}.json"


def test_trap_from_params_is_row_orthonormal_and_trapezoidal() -> None:
    rng = np.random.default_rng(0)
    for k, n in ((2, 4), (3, 6), (4, 12), (5, 10)):
        x = rng.standard_normal(nparams(k, n))
        R = trap_from_params(x, k, n)
        assert R.shape == (k, n)
        assert np.allclose(R @ R.T, np.eye(k), atol=1e-10)
        for s in range(k):
            assert np.allclose(R[s, :s], 0.0, atol=1e-12)


def test_all_tied_ansatz_is_row_orthonormal() -> None:
    for k, n in ((2, 6), (3, 9), (4, 8), (4, 12)):
        R = trap_from_params(all_tied_params(k, n), k, n)
        assert np.allclose(R @ R.T, np.eye(k), atol=1e-10)
        rec = record_instance(R, family="all_tied_ansatz", seed=0, ratio=n // k, method="all_tied")
        assert rec["aat_err"] < 1e-8
        assert rec["k"] == k and rec["n"] == n
        assert rec["inv"] > 0
        assert np.isfinite(rec["r_cpqr"])
        assert rec["named_poly"] == named_poly_scale(k, n)
        assert isinstance(rec["r_gt_1"], bool)
        assert isinstance(rec["above_named_poly"], bool)
        # Record the comparison; do not require r_cpqr < 1 or ≥ 1.
        assert rec["above_named_poly"] == (rec["inv"] >= rec["named_poly"])


def test_all_tied_fill_has_designed_equal_magnitudes() -> None:
    k, n = 3, 9
    B = all_tied_fill(k, n)
    # Last row: equal |entries| on the unused support.
    tail = B[k - 1, k - 1 :]
    assert np.allclose(np.abs(tail), np.abs(tail[0]), atol=1e-12)
    assert np.allclose(np.linalg.norm(tail), 1.0, atol=1e-12)


def test_pad_kn_preserves_param_count() -> None:
    rng = np.random.default_rng(1)
    x = rng.standard_normal(nparams(3, 6))
    y = pad_kn(x, 3, 6, 4, 8, rng=rng)
    assert y.size == nparams(4, 8)
    R = trap_from_params(y, 4, 8)
    assert np.allclose(R @ R.T, np.eye(4), atol=1e-10)


def test_small_search_runs_and_is_parseval() -> None:
    rng = np.random.default_rng(2)
    rec = search_pair(2, 4, rng, seed=2, ratio=2, include_tied=True)
    assert rec is not None
    assert rec["k"] == 2 and rec["n"] == 4
    assert rec["aat_err"] < 1e-8
    assert rec["inv"] > 0
    assert rec["sigma_min"] > 0
    assert rec["abs_det"] > 0
    assert np.isfinite(rec["r_cpqr"])
    assert rec["pivot_traj"] == [0, 1]
    assert rec["min_margin"] >= -1e-8
    assert isinstance(rec["r_gt_1"], bool)
    assert rec["above_named_poly"] is False or rec["inv"] >= rec["named_poly"]
    A = np.asarray(rec["matrix"], float)
    assert np.allclose(A @ A.T, np.eye(2), atol=1e-8)
    # The live search already required accept_matrix. Twelve-decimal
    # serialization can flip a near-tied second pivot, so do not
    # re-run CPQR on the rounded record.


def test_tiny_ladder_records_are_well_formed() -> None:
    records = run_ladder(seed=3, k_max=3, ratios=(2,), include_tied=False)
    assert len(records) >= 2
    payload = payload_from_records(records, seed=3, k_max=3, ratios=(2,))
    assert payload["seed"] == 3
    assert payload["revision"]
    assert payload["growth"]["milestone_e"] == "OPEN"
    assert "not a theorem" in payload["status"].lower() or "OPEN" in payload["status"]
    for rec in records:
        assert rec["k"] == len(rec.get("pivot_traj") or rec.get("J_cpqr") or []) or rec.get("success") is False
        if rec.get("inv") is None:
            continue
        assert rec["aat_err"] < 1e-8
        assert rec["named_poly"] == named_poly_scale(rec["k"], rec["n"])
        assert isinstance(rec["r_gt_1"], bool)
        assert isinstance(rec["above_named_poly"], bool)
        # Witness fields only — both r>1 and r≤1 are allowed.
        assert rec["r_cpqr"] > 0
        assert rec["inv"] > 0
        assert rec["sigma_min"] > 0
        assert rec["abs_det"] >= 0
    # Growth diagnosis is a fit, not a universal bound assertion.
    growth = diagnose_growth([r for r in records if r.get("inv") is not None])
    assert growth["milestone_e"] == "OPEN"
    assert "OPEN" in growth["claim"]


def test_slsqp_inequality_step_returns_feasible_point() -> None:
    x0 = all_tied_params(2, 4)
    x = slsqp_step(2, 4, x0, mode="ineq", maxiter=80)
    assert x is not None
    R = trap_from_params(x, 2, 4)
    assert np.allclose(R @ R.T, np.eye(2), atol=1e-8)
    assert float(pivot_margins(R).min()) >= -1e-8


def test_growth_fit_on_polynomial_series_is_not_a_bound() -> None:
    """A k^2 synthetic series should look polynomial; never assert r_cpqr < 1."""
    records = []
    for k in range(2, 8):
        n = 3 * k
        inv = float(k**2)
        poly = named_poly_scale(k, n)
        records.append(
            {
                "k": k,
                "n": n,
                "ratio": 3,
                "inv": inv,
                "r_cpqr": inv / (k * (n - k + 1)) ** 0.5,
                "named_poly": poly,
                "above_named_poly": inv >= poly,
                "r_gt_1": True,  # allowed; this is not a universal-bound test
            }
        )
    growth = diagnose_growth(records)
    assert growth["by_ratio"]["3"]["preferred_model"] == "polynomial-looking"
    assert growth["looks_superpolynomial"] is False
    assert growth["milestone_e"] == "OPEN"
    # The synthetic series has r>1 everywhere; that must not be forbidden.
    assert growth["any_r_gt_1"] is True
    assert all(r["r_cpqr"] > 0 for r in records)


def test_committed_json_is_well_formed_if_present() -> None:
    if not JSON_PATH.is_file():
        pytest.skip("Path 2 ladder JSON not generated yet")
    payload = json.loads(JSON_PATH.read_text())
    assert payload["seed"] == DEFAULT_SEED
    assert payload["revision"]
    assert payload["growth"]["milestone_e"] == "OPEN"
    assert payload["any_above_named_poly"] is False or any(
        r.get("above_named_poly") for r in payload["records"]
    )
    assert isinstance(payload["any_r_gt_1"], bool)
    for rec in payload["records"]:
        assert "k" in rec and "n" in rec
        assert "named_poly" in rec
        assert "r_gt_1" in rec
        assert "above_named_poly" in rec
        if rec.get("inv") is None:
            continue
        assert rec["aat_err"] < 1e-6
        assert np.isfinite(rec["r_cpqr"])
        assert rec["sigma_min"] > 0
        assert rec["abs_det"] >= 0
        # Never require a universal r_cpqr bound.
        assert isinstance(rec["r_gt_1"], bool)
        poly = rec["named_poly"] if rec["named_poly"] is not None else named_poly_scale(rec["k"], rec["n"])
        if rec["above_named_poly"]:
            assert rec["inv"] >= poly - 1e-9
    worst = payload["worst"]
    if worst is not None:
        assert worst["inv"] > 0
        assert worst["named_poly"] >= named_poly_scale(worst["k"], worst["n"]) - 1e-9
