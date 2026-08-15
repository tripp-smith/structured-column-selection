"""SPEC §8 CPQR census. Witnesses only; not a polynomial bound."""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence

import numpy as np



def named_poly_scale(k: int, n: int) -> float:
    """Named polynomial comparison from the Close-E campaign.

    ``‖A_J⁻¹‖₂ ≤ max(n³, k³, (k(n-k+1))²)`` is the threshold below
    which a certified ``r_CPQR > 1`` stays a C=1 witness and does not
    close Milestone E. This is a campaign yardstick, not a theorem.
    """
    return float(max(n**3, k**3, (k * (n - k + 1)) ** 2))


@dataclass(frozen=True)
class CensusRecord:
    family: str
    k: int
    n: int
    seed: int | None
    J_cpqr: list[int]
    J_opt: list[int] | None
    sigma_min: float
    abs_det: float
    inv_op: float
    inv_frob: float
    workshop_scale: float
    r_cpqr: float
    r_opt: float | None
    leverages: list[float]
    pivot_traj: list[int] | None = None
    aat_err: float | None = None
    unbalance: float | None = None
    named_poly: float | None = None
    inv_over_named_poly: float | None = None


def row_orthonormalize(B: np.ndarray) -> np.ndarray:
    """Return A (k×n) with A Aᵀ = I from a full-row-rank k×n matrix."""
    k, n = B.shape
    q, _ = np.linalg.qr(B.T, mode="reduced")
    A = q[:, :k].T
    return A


def haar_stiefel(k: int, n: int, rng: np.random.Generator) -> np.ndarray:
    return row_orthonormalize(rng.standard_normal((k, n)))


def hadamard_frame(k: int, n: int) -> np.ndarray:
    """First k Walsh rows on n = 2^m columns, normalized."""
    m = int(math.ceil(math.log2(n)))
    size = 1 << m
    H = np.array([[1.0]])
    while H.shape[0] < size:
        H = np.block([[H, H], [H, -H]])
    B = H[:k, :n] / math.sqrt(n)
    return row_orthonormalize(B)


def fourier_frame(k: int, n: int) -> np.ndarray:
    cols = np.arange(n)
    rows = np.arange(k)[:, None]
    B = np.cos(2 * np.pi * rows * cols / n)
    B[0] = 1.0
    return row_orthonormalize(B)


def leverage_skew_frame(k: int, n: int, skew: float = 20.0) -> np.ndarray:
    """One large-leverage direction, remaining mass spread thinly."""
    B = np.zeros((k, n))
    B[0, 0] = skew
    for i in range(1, k):
        B[i, i] = 1.0
    for j in range(k, n):
        B[:, j] = 1.0 / (skew + j)
        B[j % k, j] += 0.25
    return row_orthonormalize(B)


def near_duplicate_frame(k: int, n: int, eps: float = 1e-3) -> np.ndarray:
    """Near-duplicate of the first standard basis column, compensated."""
    B = np.zeros((k, n))
    for i in range(k):
        B[i, i] = 1.0
    if n > k:
        extra = B[:, 0].copy()
        if k > 1:
            extra = extra + eps * B[:, 1]
        B[:, k] = extra
    for j in range(k + 1, n):
        B[j % k, j] = 1.0
    return row_orthonormalize(B)


def kahan_like_frame(k: int, n: int, theta: float = 0.2) -> np.ndarray:
    """Row-orthonormalized Kahan-type block (SPEC §8 adverse construction)."""
    c = math.cos(theta)
    s = math.sin(theta)
    B = np.zeros((k, n))
    for i in range(k):
        B[i, i] = s**i
        for j in range(i + 1, k):
            B[i, j] = -c * (s**i)
    for j in range(k, n):
        B[j % k, j] = (s ** (k - 1)) * 0.5
    return row_orthonormalize(B)


def mercedes_benz() -> np.ndarray:
    """2×3 Mercedes-Benz ETF (equiangular tight frame). Already Parseval."""
    s = math.sqrt(2.0 / 3.0)
    a = 0.5 * s
    b = math.sqrt(0.5)
    return np.array([[s, -a, -a], [0.0, b, -b]], dtype=float)


def simplex_etf(k: int) -> np.ndarray:
    """Simplex ETF: k × (k+1) from ``[I | -1]``, then row-orthonormalize."""
    B = np.concatenate([np.eye(k), -np.ones((k, 1))], axis=1)
    return row_orthonormalize(B)


def icosahedral_etf() -> np.ndarray:
    """3×6 icosahedral ETF axes, then row-orthonormalize."""
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    B = np.array(
        [
            [0.0, 0.0, 1.0, 1.0, phi, phi],
            [1.0, -1.0, phi, -phi, 0.0, 0.0],
            [phi, phi, 0.0, 0.0, 1.0, -1.0],
        ],
        dtype=float,
    )
    return row_orthonormalize(B)


def paley_harmonic_frame(p: int) -> np.ndarray:
    """Real harmonic/Paley-type frame: k=(p-1)/2 rows, p columns."""
    k = (p - 1) // 2
    t = np.arange(p, dtype=float)
    rows = np.arange(1, k + 1, dtype=float)[:, None]
    B = np.cos(2.0 * math.pi * rows * t / p)
    return row_orthonormalize(B)


def clustered_near_parallels(
    k: int,
    n: int,
    eps: float = 1e-2,
    n_clusters: int | None = None,
) -> np.ndarray:
    """Tight column clusters in orthogonal coordinate planes, then QR.

    Each cluster lives in a block of rows. Columns inside a cluster are
    nearly parallel (spread ``eps``). This is the construction the
    checkpoint listed as still untested after ``AAᵀ = I``.
    """
    if n_clusters is None:
        n_clusters = max(2, k // 2)
    n_clusters = min(n_clusters, k, n)
    rows_per = max(1, k // n_clusters)
    cols_per = max(1, n // n_clusters)
    B = np.zeros((k, n))
    for c in range(n_clusters):
        r0 = c * rows_per
        r1 = k if c == n_clusters - 1 else min(k, (c + 1) * rows_per)
        j0 = c * cols_per
        j1 = n if c == n_clusters - 1 else min(n, (c + 1) * cols_per)
        dim = r1 - r0
        for t, j in enumerate(range(j0, j1)):
            B[r0, j] = 1.0
            for s in range(1, dim):
                B[r0 + s, j] = eps * math.sin((t + 1) * (s + 1.0))
    return row_orthonormalize(B)


def _inv_stats(AJ: np.ndarray) -> tuple[float, float, float, float]:
    s = np.linalg.svd(AJ, compute_uv=False)
    sigma_min = float(s[-1])
    abs_det = float(abs(np.linalg.det(AJ)))
    inv = np.linalg.inv(AJ)
    inv_op = float(np.linalg.norm(inv, 2))
    inv_frob = float(np.linalg.norm(inv, "fro"))
    return sigma_min, abs_det, inv_op, inv_frob


def _best_exhaustive(A: np.ndarray) -> tuple[list[int], float]:
    k, n = A.shape
    best_J: list[int] | None = None
    best_inv = math.inf
    from itertools import combinations

    for J in combinations(range(n), k):
        try:
            inv_op = float(np.linalg.norm(np.linalg.inv(A[:, J]), 2))
        except np.linalg.LinAlgError:
            continue
        if inv_op < best_inv:
            best_inv = inv_op
            best_J = list(J)
    if best_J is None:
        raise RuntimeError("no invertible k-set")
    return best_J, best_inv


def evaluate(A: np.ndarray, family: str, seed: int | None = None,
             exhaustive: bool = False) -> CensusRecord:
    k, n = A.shape
    traj = _cpqr_numpy_traj(A)
    J = sorted(traj)
    AJ = A[:, J]
    sigma_min, abs_det, inv_op, inv_frob = _inv_stats(AJ)
    scale = math.sqrt(k * (n - k + 1))
    r = inv_op / scale
    J_opt = None
    r_opt = None
    if exhaustive and n <= 12:
        J_opt, inv_opt = _best_exhaustive(A)
        r_opt = inv_opt / scale
    leverages = [float(np.sum(A[:, j] ** 2)) for j in range(n)]
    aat_err = float(np.max(np.abs(A @ A.T - np.eye(k))))
    unbalance = float(inv_op * abs_det)
    poly = named_poly_scale(k, n)
    return CensusRecord(
        family=family,
        k=k,
        n=n,
        seed=seed,
        J_cpqr=J,
        J_opt=J_opt,
        sigma_min=sigma_min,
        abs_det=abs_det,
        inv_op=inv_op,
        inv_frob=inv_frob,
        workshop_scale=scale,
        r_cpqr=r,
        r_opt=r_opt,
        leverages=leverages,
        pivot_traj=traj,
        aat_err=aat_err,
        unbalance=unbalance,
        named_poly=poly,
        inv_over_named_poly=inv_op / poly,
    )


def _cpqr_numpy_traj(A: np.ndarray) -> list[int]:
    k, n = A.shape
    chosen: list[int] = []
    unused = set(range(n))
    for _ in range(k):
        scores: dict[int, float] = {}
        for j in unused:
            if not chosen:
                scores[j] = float(np.sum(A[:, j] ** 2))
                continue
            B = A[:, chosen]
            gdet = float(np.linalg.det(B.T @ B))
            if abs(gdet) < 1e-14:
                scores[j] = 0.0
                continue
            B2 = np.column_stack([B, A[:, j]])
            scores[j] = float(np.linalg.det(B2.T @ B2) / gdet)
        best = max(scores.values())
        if best <= 1e-14:
            break
        j = min(idx for idx, s in scores.items() if abs(s - best) <= 1e-12 * max(1.0, abs(best)))
        chosen.append(j)
        unused.remove(j)
    return chosen


def _cpqr_numpy(A: np.ndarray) -> list[int]:
    return sorted(_cpqr_numpy_traj(A))


def run_census(seed: int = 0) -> list[CensusRecord]:
    rng = np.random.default_rng(seed)
    records: list[CensusRecord] = []
    for k, n in ((2, 5), (2, 8), (3, 6), (3, 8), (4, 8), (5, 10)):
        for i in range(4 if k >= 5 else 6):
            A = haar_stiefel(k, n, rng)
            records.append(evaluate(A, "haar_stiefel", seed=seed + i, exhaustive=n <= 8))
    for k, n in ((2, 4), (2, 8), (3, 8), (4, 8)):
        records.append(evaluate(hadamard_frame(k, n), "hadamard", exhaustive=n <= 8))
        records.append(evaluate(fourier_frame(k, n), "fourier", exhaustive=n <= 8))
        records.append(evaluate(leverage_skew_frame(k, n), "leverage_skew", exhaustive=n <= 8))
        records.append(evaluate(near_duplicate_frame(k, n), "near_duplicate", exhaustive=n <= 8))
        records.append(evaluate(kahan_like_frame(k, n), "kahan_like", exhaustive=n <= 8))
    return records


def records_to_json(records: Sequence[CensusRecord]) -> str:
    return json.dumps([asdict(r) for r in records], indent=2)


def max_r(records: Sequence[CensusRecord]) -> CensusRecord:
    return max(records, key=lambda r: r.r_cpqr)


def block_diagonal(*blocks: np.ndarray) -> np.ndarray:
    """Block-diagonal Parseval sum of already row-orthonormal blocks."""
    ks = [B.shape[0] for B in blocks]
    ns = [B.shape[1] for B in blocks]
    A = np.zeros((sum(ks), sum(ns)))
    r0 = c0 = 0
    for B, k, n in zip(blocks, ks, ns):
        A[r0 : r0 + k, c0 : c0 + n] = B
        r0 += k
        c0 += n
    return A


def run_wave1_etf() -> list[CensusRecord]:
    """Track 1: Mercedes-Benz, simplex, icosahedral, Paley/harmonic ETFs."""
    records: list[CensusRecord] = []
    records.append(evaluate(mercedes_benz(), "mercedes_benz", exhaustive=True))
    for k in (2, 3, 4, 5, 8):
        records.append(evaluate(simplex_etf(k), "simplex_etf", exhaustive=k + 1 <= 12))
    records.append(evaluate(icosahedral_etf(), "icosahedral_etf", exhaustive=True))
    for p in (5, 13, 17, 29):
        records.append(evaluate(paley_harmonic_frame(p), f"paley_harmonic_p{p}",
                                exhaustive=p <= 12))
    return records


def run_wave1_block() -> list[CensusRecord]:
    """Block-diagonal ETF copies. Witnesses only; not a bound."""
    records: list[CensusRecord] = []
    mb = mercedes_benz()
    for m in (2, 3, 4):
        records.append(
            evaluate(block_diagonal(*([mb] * m)), f"block_mb_x{m}",
                     exhaustive=3 * m <= 12)
        )
    for k1, k2 in ((2, 2), (3, 3), (4, 4), (2, 3)):
        records.append(
            evaluate(
                block_diagonal(simplex_etf(k1), simplex_etf(k2)),
                f"block_simplex_{k1}_{k2}",
                exhaustive=(k1 + k2 + 2) <= 12,
            )
        )
    return records


def run_wave1_clustered(seed: int = 1) -> list[CensusRecord]:
    """Track 2: clustered near-parallels that survive row_orthonormalize."""
    records: list[CensusRecord] = []
    configs = [
        (4, 8, 1e-1, 2),
        (4, 8, 1e-2, 2),
        (4, 8, 1e-3, 2),
        (4, 12, 1e-2, 2),
        (6, 12, 1e-2, 2),
        (6, 12, 1e-2, 3),
        (6, 12, 1e-3, 3),
        (8, 16, 1e-2, 2),
        (8, 16, 1e-2, 4),
        (8, 16, 5e-2, 4),
    ]
    for k, n, eps, ncl in configs:
        A = clustered_near_parallels(k, n, eps=eps, n_clusters=ncl)
        records.append(
            evaluate(
                A,
                f"clustered_eps{eps}_c{ncl}",
                seed=seed,
                exhaustive=n <= 12,
            )
        )
    return records


def run_wave1_growth(seed: int = 1) -> list[CensusRecord]:
    """Track 3: Haar k≥10 growth probe and n≤12 exhaustive unbalance."""
    rng = np.random.default_rng(seed)
    records: list[CensusRecord] = []
    for k, n, draws, exhaustive in (
        (8, 12, 8, True),
        (10, 12, 8, True),
        (10, 16, 6, False),
        (10, 20, 6, False),
        (12, 16, 4, False),
        (12, 24, 4, False),
    ):
        for i in range(draws):
            A = haar_stiefel(k, n, rng)
            records.append(
                evaluate(A, "haar_growth", seed=seed + i, exhaustive=exhaustive)
            )
    return records


def wave1_payload(track: str, seed: int, revision: str,
                  records: Sequence[CensusRecord]) -> dict:
    worst = max_r(records)
    return {
        "seed": seed,
        "revision": revision,
        "track": track,
        "n_records": len(records),
        "worst": asdict(worst),
        "any_r_gt_1": any(r.r_cpqr > 1 for r in records),
        "any_above_named_poly": any(
            (r.inv_over_named_poly or 0.0) >= 1.0 for r in records
        ),
        "max_aat_err": max((r.aat_err or 0.0) for r in records),
        "records": [asdict(r) for r in records],
    }


if __name__ == "__main__":
    recs = run_census(0)
    print(records_to_json(recs))
    w = max_r(recs)
    print(
        f"# worst r_CPQR={w.r_cpqr:.6f} family={w.family} k={w.k} n={w.n}",
        flush=True,
    )
