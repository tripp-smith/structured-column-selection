"""SPEC §8 census: record r_CPQR, do not assert a universal bound."""

from __future__ import annotations

import json

import numpy as np

from structselect.census import (
    block_diagonal,
    clustered_near_parallels,
    evaluate,
    fourier_frame,
    hadamard_frame,
    haar_stiefel,
    icosahedral_etf,
    kahan_like_frame,
    leverage_skew_frame,
    max_r,
    mercedes_benz,
    named_poly_scale,
    near_duplicate_frame,
    paley_harmonic_frame,
    records_to_json,
    row_orthonormalize,
    run_census,
    run_wave1_block,
    run_wave1_clustered,
    run_wave1_etf,
    simplex_etf,
)


def test_row_orthonormalize_is_parseval() -> None:
    rng = np.random.default_rng(1)
    A = row_orthonormalize(rng.standard_normal((3, 7)))
    assert np.allclose(A @ A.T, np.eye(3), atol=1e-10)


def test_generators_are_orthogonal_rows() -> None:
    rng = np.random.default_rng(2)
    frames = [
        haar_stiefel(3, 6, rng),
        hadamard_frame(2, 8),
        fourier_frame(3, 8),
        leverage_skew_frame(3, 7),
        near_duplicate_frame(3, 7),
        kahan_like_frame(3, 7),
    ]
    for A in frames:
        k = A.shape[0]
        assert np.allclose(A @ A.T, np.eye(k), atol=1e-9)


def test_census_records_are_finite_and_full_rank() -> None:
    records = run_census(seed=0)
    assert len(records) >= 20
    for rec in records:
        assert rec.k == len(rec.J_cpqr)
        assert rec.inv_op > 0
        assert rec.r_cpqr > 0
        assert np.isfinite(rec.r_cpqr)
        assert abs(sum(rec.leverages) - rec.k) < 1e-6
    payload = json.loads(records_to_json(records))
    assert payload[0]["family"]
    worst = max_r(records)
    # Census only: record the worst ratio; do not require it to be ≤ 1.
    assert worst.r_cpqr > 0


def test_evaluate_small_exhaustive_compares_opt() -> None:
    A = hadamard_frame(2, 4)
    rec = evaluate(A, "hadamard", exhaustive=True)
    assert rec.J_opt is not None
    assert rec.r_opt is not None
    assert rec.r_opt <= rec.r_cpqr + 1e-9


def test_wave1_etf_generators_are_parseval() -> None:
    frames = [
        mercedes_benz(),
        simplex_etf(3),
        icosahedral_etf(),
        paley_harmonic_frame(5),
        clustered_near_parallels(4, 8, eps=1e-2, n_clusters=2),
        block_diagonal(mercedes_benz(), mercedes_benz()),
    ]
    for A in frames:
        k = A.shape[0]
        assert np.allclose(A @ A.T, np.eye(k), atol=1e-9)


def test_wave1_etf_records_are_finite() -> None:
    records = run_wave1_etf()
    assert len(records) >= 8
    for rec in records:
        assert rec.k == len(rec.J_cpqr)
        assert rec.inv_op > 0
        assert rec.r_cpqr > 0
        assert np.isfinite(rec.r_cpqr)
        assert rec.aat_err is not None and rec.aat_err < 1e-8
        assert rec.pivot_traj is not None and len(rec.pivot_traj) == rec.k
        # Census only: record the ratio; do not require it to be ≤ 1.
        assert rec.named_poly == named_poly_scale(rec.k, rec.n)


def test_wave1_block_records_are_finite() -> None:
    records = run_wave1_block()
    assert len(records) >= 4
    worst = max_r(records)
    assert worst.r_cpqr > 0
    assert np.isfinite(worst.r_cpqr)
    for rec in records:
        assert rec.aat_err is not None and rec.aat_err < 1e-8


def test_wave1_clustered_records_are_finite() -> None:
    records = run_wave1_clustered(seed=1)
    assert len(records) >= 6
    worst = max_r(records)
    assert worst.r_cpqr > 0
    assert np.isfinite(worst.r_cpqr)
    for rec in records:
        assert rec.aat_err is not None and rec.aat_err < 1e-8
