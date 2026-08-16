"""Path 2 trapezoidal search for adverse row-orthonormal CPQR instances.

Python witnesses only. This module does **not** prove a polynomial bound,
does **not** certify a superpolynomial family, and does **not** close
Milestone E. A recorded ``r_CPQR > 1`` is a C=1 (workshop-scale) witness
unless the inverse norm exceeds ``named_poly_scale`` or a certified
growing family is superpolynomial.
"""

from __future__ import annotations

import json
import math
import subprocess
from dataclasses import asdict
from pathlib import Path
from typing import Any, Sequence

import numpy as np
from scipy.optimize import minimize

from structselect.census import evaluate, named_poly_scale

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SEED = 20260816
NUMERIC_412 = ROOT / "experiments" / "cpqr_r_gt_1_numeric_4_12.json"


def nparams(k: int, n: int) -> int:
    """Number of free entries in a k×n upper-trapezoidal fill."""
    return k * n - k * (k - 1) // 2


def unpack_trap(x: np.ndarray, k: int, n: int) -> np.ndarray:
    """Scatter a parameter vector into a k×n fill with zeros for column t < row s."""
    B = np.zeros((k, n))
    idx = 0
    for s in range(k):
        m = n - s
        B[s, s:] = x[idx : idx + m]
        idx += m
    return B


def params_from_trap(B: np.ndarray) -> np.ndarray:
    k, n = B.shape
    parts = [B[s, s:].ravel() for s in range(k)]
    return np.concatenate(parts) if parts else np.zeros(0)


def trap_from_params(x: np.ndarray, k: int, n: int) -> np.ndarray:
    """Reverse Gram–Schmidt: row-orthonormal k×n matrix, R[s, t] = 0 for t < s."""
    B = unpack_trap(np.asarray(x, float), k, n)
    R = np.zeros((k, n))
    for s in range(k - 1, -1, -1):
        v = B[s].copy()
        for t in range(s + 1, k):
            v -= (v @ R[t]) * R[t]
        nv = float(np.linalg.norm(v))
        if nv < 1e-12:
            v = np.zeros(n)
            v[s] = 1.0
            for t in range(s + 1, k):
                v -= (v @ R[t]) * R[t]
            nv = float(np.linalg.norm(v))
            if nv < 1e-12:
                continue
        R[s] = v / nv
    return R


def to_trapezoidal(A: np.ndarray) -> np.ndarray:
    """Left-rotate so the leading k×k block is upper triangular (row-orthonormal)."""
    k, _n = A.shape
    q, _r = np.linalg.qr(A[:, :k], mode="reduced")
    return q.T @ A


def pivot_margins(R: np.ndarray) -> np.ndarray:
    """``res_s(s) - res_s(j)`` for j > s. Nonnegative forces CPQR pivots 0..k-1."""
    k, n = R.shape
    out: list[float] = []
    for s in range(k):
        res = (R[s:, :] ** 2).sum(0)
        for j in range(s + 1, n):
            out.append(float(res[s] - res[j]))
    return np.asarray(out, float)


def residual_energy_floor(s: int, k: int, n: int) -> float:
    """Equal-residual value ``(k-s)/(n-s)`` on the all-tied boundary."""
    return (k - s) / (n - s)


def all_tied_fill(k: int, n: int) -> np.ndarray:
    """Kahan-signed trapezoidal fill with all-tied residual magnitudes.

    At step ``s`` the unused residual mass ``k-s`` is spread equally over
    ``n-s`` columns, so every unused margin is designed to be ~0 *before*
    reverse Gram–Schmidt. Reverse GS is still required for ``AAᵀ = I``.
    """
    B = np.zeros((k, n))
    for s in range(k):
        d_s = residual_energy_floor(s, k, n)
        B[s, s] = math.sqrt(d_s)
        if s + 1 < k:
            d_next = residual_energy_floor(s + 1, k, n)
            off = math.sqrt(max(d_s - d_next, 0.0))
        else:
            off = math.sqrt(d_s)
        B[s, s + 1 :] = -off
    return B


def all_tied_params(k: int, n: int) -> np.ndarray:
    return params_from_trap(all_tied_fill(k, n))


def kahan_fill(k: int, n: int, theta: float = 0.2) -> np.ndarray:
    """Classical Kahan pattern on the leading block, tiny tail; not orthonormal yet."""
    c = math.cos(theta)
    s = math.sin(theta)
    B = np.zeros((k, n))
    for i in range(k):
        B[i, i] = s**i
        for j in range(i + 1, min(k, n)):
            B[i, j] = -c * (s**i)
        for j in range(k, n):
            B[i, j] = -c * (s**i) * 0.25
    return B


def kahan_params(k: int, n: int, theta: float = 0.2) -> np.ndarray:
    return params_from_trap(kahan_fill(k, n, theta=theta))


def pad_columns(x: np.ndarray, k: int, n: int, extra: int, fill: float = 0.05) -> np.ndarray:
    """Lift (k, n) parameters to (k, n+extra) by appending ``fill`` on each row."""
    if extra <= 0:
        return np.asarray(x, float)
    out: list[float] = []
    idx = 0
    xv = np.asarray(x, float)
    for s in range(k):
        m = n - s
        out.extend(xv[idx : idx + m].tolist())
        out.extend([fill] * extra)
        idx += m
    return np.asarray(out, float)


def pad_row(x: np.ndarray, k: int, n: int, rng: np.random.Generator | None = None) -> np.ndarray:
    """Lift (k, n) parameters to (k+1, n) by appending a new last row."""
    extra = n - k
    if rng is None:
        tail = np.zeros(extra)
        if extra:
            tail[0] = 1.0
            if extra > 1:
                tail[1:] = -1.0 / math.sqrt(extra)
    else:
        tail = 0.3 * rng.standard_normal(extra)
        if extra:
            tail[0] = abs(float(tail[0])) + 0.5
    return np.concatenate([np.asarray(x, float), tail])


def pad_kn(
    x: np.ndarray,
    k: int,
    n: int,
    k_new: int,
    n_new: int,
    rng: np.random.Generator | None = None,
) -> np.ndarray:
    """Pad a (k, n) parameter vector to (k_new, n_new) with k_new≥k, n_new≥n."""
    cur = np.asarray(x, float)
    ck, cn = k, n
    while cn < n_new:
        cur = pad_columns(cur, ck, cn, 1)
        cn += 1
    while ck < k_new:
        cur = pad_row(cur, ck, cn, rng=rng)
        ck += 1
    if cur.size != nparams(k_new, n_new):
        raise ValueError(
            f"pad_kn size {cur.size} != nparams({k_new},{n_new})={nparams(k_new, n_new)}"
        )
    return cur


def warm_params_from_numeric_412() -> np.ndarray | None:
    """Optional warm start from the repo's numeric 4×12 r>1 record (not certified)."""
    if not NUMERIC_412.is_file():
        return None
    data = json.loads(NUMERIC_412.read_text())
    A = np.asarray(data["matrix"], float)
    return params_from_trap(to_trapezoidal(A))


def _objective_log_smin(x: np.ndarray, k: int, n: int) -> float:
    R = trap_from_params(x, k, n)
    smin = float(np.linalg.svd(R[:, :k], compute_uv=False)[-1])
    return math.log(max(smin, 1e-300))


def _objective_tied(x: np.ndarray, k: int, n: int, lam: float) -> float:
    """Maximise inverse norm while driving unused pivot margins to 0."""
    R = trap_from_params(x, k, n)
    smin = float(np.linalg.svd(R[:, :k], compute_uv=False)[-1])
    m = pivot_margins(R)
    slack = float(np.mean(np.maximum(m, 0.0) ** 2))
    return math.log(max(smin, 1e-300)) + lam * slack


def slsqp_step(
    k: int,
    n: int,
    x0: np.ndarray,
    *,
    mode: str = "ineq",
    eta: float = 0.0,
    lam: float = 25.0,
    maxiter: int = 200,
) -> np.ndarray | None:
    """One SLSQP attempt. ``mode`` is ``ineq`` (CPQR-feasible) or ``tied`` (all-tied)."""
    x0 = np.asarray(x0, float).ravel()
    if x0.size != nparams(k, n):
        return None

    def cons_fun(x: np.ndarray) -> np.ndarray:
        return pivot_margins(trap_from_params(x, k, n)) - eta

    cons = [{"type": "ineq", "fun": cons_fun}]
    if mode == "tied":
        fun = lambda x: _objective_tied(x, k, n, lam)
    else:
        fun = lambda x: _objective_log_smin(x, k, n)
    try:
        res = minimize(
            fun,
            x0,
            constraints=cons,
            method="SLSQP",
            options={"maxiter": maxiter, "ftol": 1e-12, "disp": False, "eps": 1e-6},
        )
    except Exception:
        return None
    return np.asarray(res.x, float)


def accept_matrix(R: np.ndarray, eta: float = 0.0) -> bool:
    """True when AAᵀ ≈ I, margins allow pivots 0..k-1, and CPQR agrees."""
    k, _n = R.shape
    aat_err = float(np.max(np.abs(R @ R.T - np.eye(k))))
    if aat_err > 1e-8:
        return False
    if float(pivot_margins(R).min(initial=0.0)) < eta - 1e-8:
        return False
    rec = evaluate(R, family="accept_check")
    return rec.pivot_traj == list(range(k))


def record_instance(
    R: np.ndarray,
    *,
    family: str,
    seed: int,
    ratio: int | None,
    method: str,
) -> dict[str, Any]:
    rec = evaluate(R, family=family, seed=seed, exhaustive=False)
    d = asdict(rec)
    poly = rec.named_poly if rec.named_poly is not None else named_poly_scale(rec.k, rec.n)
    inv = rec.inv_op
    d.update(
        inv=inv,
        ratio=ratio,
        method=method,
        min_margin=float(pivot_margins(R).min(initial=0.0)),
        r_gt_1=bool(rec.r_cpqr > 1.0),
        above_named_poly=bool(inv >= poly),
        n_params=nparams(rec.k, rec.n),
        matrix=np.round(R, 12).tolist(),
    )
    return d


def _restart_budget(k: int) -> tuple[int, int]:
    """``(n_random, maxiter)`` modest enough to finish k≤8, n≤24."""
    if k <= 3:
        return 6, 180
    if k <= 5:
        return 4, 120
    if k <= 6:
        return 3, 90
    return 5, 100


def strictify(R: np.ndarray, eps: float = 1e-5) -> np.ndarray:
    """Nudge intended pivots so CPQR's smallest-index tie-break is unambiguous."""
    k, n = R.shape
    B = R.copy()
    for s in range(k):
        B[s, s] += eps
    return trap_from_params(params_from_trap(B), k, n)


def embed_prev_params(prev_R: np.ndarray, k_new: int, n_new: int) -> np.ndarray:
    """Place a smaller feasible R in the leading block and complete the diagonal."""
    k, n = prev_R.shape
    B = np.zeros((k_new, n_new))
    B[:k, :n] = prev_R
    for s in range(k, k_new):
        if s < n_new:
            B[s, s] = 1.0
    return params_from_trap(B)


def structured_starts(
    k: int,
    n: int,
    rng: np.random.Generator,
    prev_x: np.ndarray | None,
    prev_kn: tuple[int, int] | None,
) -> list[np.ndarray]:
    starts: list[np.ndarray] = [
        all_tied_params(k, n),
        kahan_params(k, n, theta=0.15),
        kahan_params(k, n, theta=0.35),
    ]
    if prev_x is not None and prev_kn is not None:
        pk, pn = prev_kn
        try:
            starts.append(pad_kn(prev_x, pk, pn, k, n, rng=None))
            starts.append(pad_kn(prev_x, pk, pn, k, n, rng=rng))
            prev_R = trap_from_params(prev_x, pk, pn)
            starts.append(embed_prev_params(prev_R, k, n))
            starts.append(params_from_trap(strictify(trap_from_params(embed_prev_params(prev_R, k, n), k, n))))
        except ValueError:
            pass
    if (k, n) == (4, 12):
        w = warm_params_from_numeric_412()
        if w is not None:
            starts.append(w)
    n_rand, _maxiter = _restart_budget(k)
    starts.extend(rng.standard_normal(nparams(k, n)) for _ in range(n_rand))
    return starts


def search_pair(
    k: int,
    n: int,
    rng: np.random.Generator,
    *,
    seed: int,
    ratio: int | None,
    prev_x: np.ndarray | None = None,
    prev_kn: tuple[int, int] | None = None,
    include_tied: bool = True,
) -> dict[str, Any] | None:
    """Maximise ‖A_J⁻¹‖₂ over trapezoidal Stiefel matrices with CPQR pivots 0..k-1."""
    _n_rand, maxiter = _restart_budget(k)
    best: dict[str, Any] | None = None
    best_x: np.ndarray | None = None

    def consider(x: np.ndarray, method: str) -> None:
        nonlocal best, best_x
        candidates = [np.asarray(x, float)]
        R0 = trap_from_params(x, k, n)
        candidates.append(params_from_trap(strictify(R0)))
        for xv in candidates:
            R = trap_from_params(xv, k, n)
            if not accept_matrix(R):
                continue
            rec = record_instance(
                R, family=f"adverse_{method}", seed=seed, ratio=ratio, method=method
            )
            if best is None or rec["inv"] > best["inv"]:
                best = rec
                best_x = np.asarray(xv, float).copy()

    starts = structured_starts(k, n, rng, prev_x, prev_kn)
    tied_cap = 3 if include_tied else 0
    for i, x0 in enumerate(starts):
        consider(np.asarray(x0, float), "start")
        x = slsqp_step(k, n, x0, mode="ineq", maxiter=maxiter)
        if x is not None:
            consider(x, "ladder")
        # All-tied SLSQP only on the structured ansatz / warm starts, not every
        # random restart — otherwise k=8, n=24 does not finish.
        if i < tied_cap:
            xt = slsqp_step(k, n, x0, mode="tied", maxiter=max(40, maxiter // 2))
            if xt is not None:
                consider(xt, "all_tied")

    if best is not None and best_x is not None:
        best["x"] = best_x.tolist()
    return best


def diagnose_growth(records: Sequence[dict[str, Any]]) -> dict[str, Any]:
    """Compare power-law vs exponential fits of inv vs k. Observation only."""
    by_ratio: dict[str, Any] = {}
    any_above = False
    any_r = False
    looks_super = False
    for rec in records:
        any_above = any_above or bool(rec.get("above_named_poly"))
        any_r = any_r or bool(rec.get("r_gt_1"))
    ratios = sorted({int(r["ratio"]) for r in records if r.get("ratio") is not None})
    for ratio in ratios:
        rows = [r for r in records if r.get("ratio") == ratio and r.get("inv") is not None]
        rows = sorted(rows, key=lambda r: (r["k"], -r["inv"]))
        # one best inv per k
        best_at_k: dict[int, dict[str, Any]] = {}
        for r in rows:
            if r["k"] not in best_at_k:
                best_at_k[r["k"]] = r
        ks = np.array(sorted(best_at_k), float)
        invs = np.array([best_at_k[int(k)]["inv"] for k in ks], float)
        rs = np.array([best_at_k[int(k)]["r_cpqr"] for k in ks], float)
        named = np.array(
            [best_at_k[int(k)]["named_poly"] or named_poly_scale(int(k), int(best_at_k[int(k)]["n"]))
             for k in ks],
            float,
        )
        entry: dict[str, Any] = {
            "ks": [int(k) for k in ks],
            "invs": [float(v) for v in invs],
            "r_cpqr": [float(v) for v in rs],
            "named_poly": [float(v) for v in named],
            "inv_over_named_poly": [float(i / p) for i, p in zip(invs, named)],
            "inv_over_named_poly_trend": (
                "decreasing"
                if len(invs) >= 2 and (invs[-1] / named[-1]) < (invs[0] / named[0])
                else "non-decreasing"
            ),
            "max_inv": float(invs.max()) if len(invs) else None,
            "max_r_cpqr": float(rs.max()) if len(rs) else None,
            "any_r_gt_1": bool((rs > 1.0).any()) if len(rs) else False,
            "any_above_named_poly": bool((invs >= named).any()) if len(invs) else False,
        }
        preferred = "inconclusive"
        if len(ks) >= 3:
            logk = np.log(ks)
            logi = np.log(np.maximum(invs, 1e-300))
            b_pow, a_pow = np.polyfit(logk, logi, 1)
            b_exp, a_exp = np.polyfit(ks, logi, 1)
            rss_pow = float(np.mean((logi - (a_pow + b_pow * logk)) ** 2))
            rss_exp = float(np.mean((logi - (a_exp + b_exp * ks)) ** 2))
            entry["loglog_slope"] = float(b_pow)
            entry["loglin_slope"] = float(b_exp)
            entry["rss_power"] = rss_pow
            entry["rss_exponential"] = rss_exp
            # Superpolynomial *looking* only if exponential clearly fits better
            # *and* inv grows faster than a high-degree power of k on this range.
            # A short k≤8 window often makes exp-RSS slightly better even when
            # the power-law slope is O(1)–O(2); that is still polynomial-looking.
            poly_ratio = float(invs[-1] / named[-1]) if named[-1] else 0.0
            if b_pow <= 4.0 and poly_ratio < 0.05:
                preferred = "polynomial-looking"
            elif rss_exp < 0.25 * rss_pow and b_exp > 0.4:
                preferred = "exponential-looking"
            elif b_pow <= 6.0:
                preferred = "polynomial-looking"
            else:
                preferred = "high-degree-or-faster"
        # A family that stays far below named_poly is not a poly(n,k) disproof,
        # even if an exponential fit is slightly better on k≤8.
        entry["preferred_model"] = preferred
        entry["looks_superpolynomial"] = bool(
            preferred == "exponential-looking" and entry["any_above_named_poly"]
        )
        entry["note"] = (
            "k≤8 ladder is too short to certify superpolynomial growth. "
            "preferred_model is a numeric fit, not a theorem. "
            "Crossing named_poly_scale or a certified superpolynomial family "
            "would be required to close Path 2; this ratio does not."
            if not entry["any_above_named_poly"]
            else "An instance met or exceeded named_poly_scale (still not a Lean certificate)."
        )
        looks_super = looks_super or bool(entry["looks_superpolynomial"])
        by_ratio[str(ratio)] = entry
    return {
        "by_ratio": by_ratio,
        "any_r_gt_1": any_r,
        "any_above_named_poly": any_above,
        "looks_superpolynomial": looks_super,
        "milestone_e": "OPEN",
        "claim": (
            "Research observation only. A single r_CPQR>1 is a C=1 witness. "
            "No certified superpolynomial family and no named-poly breach "
            "is claimed here. Milestone E stays OPEN."
        ),
    }


def git_revision() -> str:
    try:
        out = subprocess.check_output(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=ROOT,
            text=True,
        )
        return out.strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def run_ladder(
    *,
    seed: int = DEFAULT_SEED,
    k_max: int = 8,
    ratios: Sequence[int] = (2, 3),
    include_tied: bool = True,
    verbose: bool = False,
) -> list[dict[str, Any]]:
    """Warm-started ladder in k at n = ratio·k. Records are witnesses, not theorems."""
    rng = np.random.default_rng(seed)
    records: list[dict[str, Any]] = []
    for ratio in ratios:
        prev_x: np.ndarray | None = None
        prev_kn: tuple[int, int] | None = None
        for k in range(2, k_max + 1):
            n = ratio * k
            if n <= k:
                continue
            if verbose:
                print(f"# searching k={k} n={n} ratio={ratio}", flush=True)
            got = search_pair(
                k,
                n,
                rng,
                seed=seed,
                ratio=ratio,
                prev_x=prev_x,
                prev_kn=prev_kn,
                include_tied=include_tied,
            )
            if got is None:
                if verbose:
                    print(f"#   failed k={k} n={n}", flush=True)
                records.append(
                    {
                        "family": "adverse_search_failed",
                        "k": k,
                        "n": n,
                        "seed": seed,
                        "ratio": ratio,
                        "method": "ladder",
                        "inv": None,
                        "r_cpqr": None,
                        "sigma_min": None,
                        "abs_det": None,
                        "aat_err": None,
                        "named_poly": named_poly_scale(k, n),
                        "r_gt_1": False,
                        "above_named_poly": False,
                        "success": False,
                    }
                )
                continue
            got["success"] = True
            records.append(got)
            if verbose:
                print(
                    f"#   inv={got['inv']:.4f} r={got['r_cpqr']:.4f} "
                    f"method={got['method']} above_poly={got['above_named_poly']}",
                    flush=True,
                )
            if "x" in got:
                prev_x = np.asarray(got["x"], float)
                prev_kn = (k, n)
    return records


def payload_from_records(
    records: Sequence[dict[str, Any]],
    *,
    seed: int,
    revision: str | None = None,
    k_max: int = 8,
    ratios: Sequence[int] = (2, 3),
) -> dict[str, Any]:
    successful = [r for r in records if r.get("inv") is not None]
    growth = diagnose_growth(successful)
    worst = max(successful, key=lambda r: r["inv"]) if successful else None
    # Drop the raw parameter vector from the published JSON (keep matrix).
    published = []
    for r in records:
        q = dict(r)
        q.pop("x", None)
        published.append(q)
    return {
        "experiment": "path2_adverse_trapezoidal_ladder",
        "status": (
            "NUMERICALLY OBSERVED (not a theorem; not a certified "
            "counterexample family; Milestone E stays OPEN)"
        ),
        "seed": seed,
        "revision": revision or git_revision(),
        "k_max": k_max,
        "n_max": max((r["n"] for r in records), default=None),
        "ratios": list(ratios),
        "n_records": len(records),
        "n_successful": len(successful),
        "any_r_gt_1": growth["any_r_gt_1"],
        "any_above_named_poly": growth["any_above_named_poly"],
        "growth": growth,
        "worst": None
        if worst is None
        else {k: v for k, v in worst.items() if k != "x"},
        "records": published,
        "note": (
            "Trapezoidal reverse-GS search with CPQR pivot-margin constraints "
            "and an all-tied (margin≈0) ansatz. Compare inv to named_poly_scale "
            "= max(n³, k³, (k(n-k+1))²). r>1 kills only C=1. E stays OPEN."
        ),
    }


def run_path2(
    *,
    seed: int = DEFAULT_SEED,
    k_max: int = 8,
    ratios: Sequence[int] = (2, 3),
    include_tied: bool = True,
    verbose: bool = False,
) -> dict[str, Any]:
    records = run_ladder(
        seed=seed,
        k_max=k_max,
        ratios=ratios,
        include_tied=include_tied,
        verbose=verbose,
    )
    return payload_from_records(
        records, seed=seed, k_max=k_max, ratios=ratios
    )


def default_json_path(seed: int = DEFAULT_SEED) -> Path:
    return ROOT / "experiments" / f"cpqr_adverse_ladder_seed{seed}.json"


def write_experiment(
    path: Path | None = None,
    *,
    seed: int = DEFAULT_SEED,
    k_max: int = 8,
    ratios: Sequence[int] = (2, 3),
    verbose: bool = False,
) -> Path:
    payload = run_path2(
        seed=seed, k_max=k_max, ratios=ratios, verbose=verbose
    )
    out = path or default_json_path(seed)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2))
    return out


if __name__ == "__main__":
    dest = write_experiment(verbose=True)
    payload = json.loads(dest.read_text())
    print(f"wrote {dest}")
    print(f"revision={payload['revision']} seed={payload['seed']}")
    print(f"any_r_gt_1={payload['any_r_gt_1']} "
          f"any_above_named_poly={payload['any_above_named_poly']}")
    print(f"growth.looks_superpolynomial={payload['growth']['looks_superpolynomial']}")
    print(f"milestone_e={payload['growth']['milestone_e']}")
    if payload["worst"]:
        w = payload["worst"]
        print(
            f"worst inv={w['inv']:.6f} r_cpqr={w['r_cpqr']:.6f} "
            f"k={w['k']} n={w['n']} method={w['method']}"
        )
