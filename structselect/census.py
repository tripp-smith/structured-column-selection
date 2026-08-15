"""SPEC §8 CPQR census. Witnesses only; not a polynomial bound."""

from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence

import numpy as np



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
    J = _cpqr_numpy(A)
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
    )


def _cpqr_numpy(A: np.ndarray) -> list[int]:
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
    return sorted(chosen)


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


if __name__ == "__main__":
    recs = run_census(0)
    print(records_to_json(recs))
    w = max_r(recs)
    print(
        f"# worst r_CPQR={w.r_cpqr:.6f} family={w.family} k={w.k} n={w.n}",
        flush=True,
    )
