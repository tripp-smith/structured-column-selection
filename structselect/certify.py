"""SPEC §9 rational certificate automation.

Turn a numeric ``k×n`` row-orthonormal-ish matrix (or a free generator
``B``) into an exact rational frame with ``AAᵀ = I`` in ``ℚ``, then
certify the CPQR counterexample protocol:

1. ``AAᵀ = I`` exactly;
2. every CPQR pivot has a strictly positive margin (unique maximizer);
3. an explicit rational test vector with ``c · ‖A_J x‖² < ‖x‖²``,
   hence ``σ_min² < 1/c`` and ``‖A_J⁻¹‖₂ > √c``.

Re-parametrization uses the Cayley transform of a rational
skew-symmetric matrix (coefficient denominator ``D``) and/or rational
Givens rotations from Pythagorean triples (the 2-D Cayley / Weierstrass
map on the circle).

This module does **not** close Milestone E. A certified ``r_CPQR > 1``
witness refutes only the ideal ``C = 1`` workshop-scale bound unless
the inverse-norm lower bound exceeds the campaign's named polynomial
``max(n³, k³, (k(n-k+1))²)``.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Sequence

import numpy as np

from structselect.census import named_poly_scale, row_orthonormalize
from structselect.cpqr import det, matmul, residual_sq, transpose

MatrixQ = list[list[Fraction]]
VecQ = list[Fraction]

__all__ = [
    "Certificate",
    "CertificationError",
    "cayley",
    "cayley_stiefel",
    "certify",
    "certify_json_record",
    "circle_point_from_half_tan",
    "complete_orthogonal",
    "givens_plane",
    "inverse_cayley",
    "inverse_norm_test_vector",
    "is_row_orthonormal",
    "lean_rat",
    "nearest_pythagorean",
    "pivot_certificate",
    "pythagorean_cs",
    "reparametrize",
    "reparametrize_cayley",
    "reparametrize_givens",
    "skew_from_upper",
    "workshop_c",
]


class CertificationError(ValueError):
    """Raised when a SPEC §9 check cannot be completed."""


# ---------------------------------------------------------------------------
# Exact linear algebra over ℚ
# ---------------------------------------------------------------------------


def eye(n: int) -> MatrixQ:
    return [[Fraction(i == j) for j in range(n)] for i in range(n)]


def zeros(m: int, n: int) -> MatrixQ:
    return [[Fraction(0) for _ in range(n)] for _ in range(m)]


def to_fraction(x: Fraction | int | str | float) -> Fraction:
    if isinstance(x, Fraction):
        return x
    if isinstance(x, int):
        return Fraction(x)
    if isinstance(x, str):
        return Fraction(x)
    return Fraction(x).limit_denominator()


def matrix_q(
    rows: Sequence[Sequence[Fraction | int | str | float]],
) -> MatrixQ:
    return [[to_fraction(v) for v in row] for row in rows]


def mat_add(A: MatrixQ, B: MatrixQ) -> MatrixQ:
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A: MatrixQ, B: MatrixQ) -> MatrixQ:
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def matvec(A: MatrixQ, x: Sequence[Fraction]) -> VecQ:
    return [sum(A[i][j] * x[j] for j in range(len(x))) for i in range(len(A))]


def norm_sq(x: Sequence[Fraction]) -> Fraction:
    return sum(v * v for v in x)


def invert(M: MatrixQ) -> MatrixQ:
    """Gaussian–Jordan inverse over ``ℚ``. ``M`` must be square and invertible."""
    n = len(M)
    if any(len(row) != n for row in M):
        raise CertificationError("invert expects a square matrix")
    a = [list(row) + [Fraction(i == j) for j in range(n)] for i, row in enumerate(M)]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(a[r][col]))
        if a[piv][col] == 0:
            raise CertificationError("singular matrix in invert")
        a[col], a[piv] = a[piv], a[col]
        div = a[col][col]
        a[col] = [x / div for x in a[col]]
        for r in range(n):
            if r == col:
                continue
            f = a[r][col]
            if f == 0:
                continue
            a[r] = [a[r][c] - f * a[col][c] for c in range(2 * n)]
    return [row[n:] for row in a]


def max_denominator(A: MatrixQ) -> int:
    return max((x.denominator for row in A for x in row), default=1)


def aat(A: MatrixQ) -> MatrixQ:
    return matmul(A, transpose(A))


def is_identity(G: MatrixQ) -> bool:
    n = len(G)
    return all(G[i][j] == (Fraction(1) if i == j else Fraction(0))
               for i in range(n) for j in range(n))


def is_row_orthonormal(A: MatrixQ) -> bool:
    return is_identity(aat(A))


def is_skew_symmetric(S: MatrixQ) -> bool:
    n = len(S)
    return all(S[i][j] == -S[j][i] for i in range(n) for j in range(n))


def workshop_c(k: int, n: int) -> int:
    """``k(n-k+1)``: the squared workshop scale. ``c · σ_min² < 1`` ⇒ ``r_CPQR > 1``."""
    return k * (n - k + 1)


# ---------------------------------------------------------------------------
# Cayley transform
# ---------------------------------------------------------------------------


def skew_from_upper(n: int, upper: Sequence[Fraction]) -> MatrixQ:
    """Build an ``n×n`` skew-symmetric matrix from the strict upper triangle.

    ``upper`` is the row-major list of entries ``S[i,j]`` for ``0 ≤ i < j < n``,
    length ``n(n-1)/2``.
    """
    need = n * (n - 1) // 2
    if len(upper) != need:
        raise CertificationError(f"expected {need} upper entries, got {len(upper)}")
    S = zeros(n, n)
    it = iter(upper)
    for i in range(n):
        for j in range(i + 1, n):
            a = to_fraction(next(it))
            S[i][j] = a
            S[j][i] = -a
    return S


def project_skew(S: MatrixQ) -> MatrixQ:
    """Force skew-symmetry by averaging ``(S - Sᵀ)/2`` and zeroing the diagonal."""
    n = len(S)
    out = zeros(n, n)
    for i in range(n):
        for j in range(i + 1, n):
            a = (S[i][j] - S[j][i]) / 2
            out[i][j] = a
            out[j][i] = -a
    return out


def cayley(S: MatrixQ) -> MatrixQ:
    """``Q = (I - S)(I + S)⁻¹``. If ``Sᵀ = -S`` and ``I+S`` is invertible, ``Q`` is orthogonal."""
    n = len(S)
    I = eye(n)
    return matmul(mat_sub(I, S), invert(mat_add(I, S)))


def inverse_cayley(Q: MatrixQ) -> MatrixQ:
    """``S = (I - Q)(I + Q)⁻¹``. Requires ``-1`` not an eigenvalue of ``Q``."""
    n = len(Q)
    I = eye(n)
    return matmul(mat_sub(I, Q), invert(mat_add(I, Q)))


def cayley_stiefel(S: MatrixQ, k: int) -> MatrixQ:
    """First ``k`` rows of ``cayley(S)``: a rational ``k×n`` row-orthonormal frame."""
    Q = cayley(S)
    if not (1 <= k <= len(Q)):
        raise CertificationError(f"k={k} out of range for n={len(Q)}")
    return [row[:] for row in Q[:k]]


def rationalize_coeff(x: float, denominator: int) -> Fraction:
    """Nearest rational with coefficient denominator ``D`` (then reduced)."""
    if denominator <= 0:
        raise CertificationError("denominator must be positive")
    return Fraction(round(x * denominator), denominator)


def rationalize_matrix_coeff(M: np.ndarray, denominator: int) -> MatrixQ:
    return [
        [rationalize_coeff(float(M[i, j]), denominator) for j in range(M.shape[1])]
        for i in range(M.shape[0])
    ]


# ---------------------------------------------------------------------------
# Rational Givens / Pythagorean triples
# ---------------------------------------------------------------------------


def pythagorean_cs(m: int, n: int) -> tuple[Fraction, Fraction]:
    """Primitive-style rational point: ``c = (m²-n²)/(m²+n²)``, ``s = 2mn/(m²+n²)``."""
    if m == 0 and n == 0:
        raise CertificationError("degenerate Pythagorean generators")
    mm, nn = m * m, n * n
    den = mm + nn
    return Fraction(mm - nn, den), Fraction(2 * m * n, den)


def circle_point_from_half_tan(t: Fraction) -> tuple[Fraction, Fraction]:
    """Weierstrass / 2-D Cayley: ``c = (1-t²)/(1+t²)``, ``s = 2t/(1+t²)``."""
    tt = t * t
    den = Fraction(1) + tt
    return (Fraction(1) - tt) / den, (2 * t) / den


def nearest_pythagorean(
    c: float, s: float, max_den: int = 10_000
) -> tuple[Fraction, Fraction]:
    """Nearest rational point on the circle to a (possibly unnormalized) pair.

    Uses the half-angle parameter ``t = s/(1+c)`` (stereographic from ``(-1,0)``)
    and ``Fraction.limit_denominator``. The output satisfies ``c² + s² = 1``
    exactly in ``ℚ``.
    """
    r = math.hypot(c, s)
    if r == 0.0:
        return Fraction(1), Fraction(0)
    c /= r
    s /= r
    if c > -0.999:
        t = s / (1.0 + c)
    elif abs(s) > 1e-18:
        t = (1.0 - c) / s
    else:
        return Fraction(-1), Fraction(0)
    tQ = Fraction(t).limit_denominator(max_den)
    return circle_point_from_half_tan(tQ)


def givens_plane(n: int, i: int, j: int, c: Fraction, s: Fraction) -> MatrixQ:
    """``n×n`` Givens rotation in the ``(i,j)`` plane. Requires ``c²+s² = 1``."""
    if c * c + s * s != 1:
        raise CertificationError("Givens (c,s) must lie on the unit circle")
    G = eye(n)
    G[i][i] = c
    G[i][j] = s
    G[j][i] = -s
    G[j][j] = c
    return G


def apply_givens_rows(
    M: list[list[Fraction]], i: int, j: int, c: Fraction, s: Fraction
) -> None:
    """In-place: rows ``(i,j) ← ((c,s), (-s,c))`` applied to ``M``."""
    cols = len(M[0])
    ri, rj = M[i], M[j]
    for q in range(cols):
        a, b = ri[q], rj[q]
        ri[q] = c * a + s * b
        rj[q] = -s * a + c * b


# ---------------------------------------------------------------------------
# Numeric → rational Stiefel
# ---------------------------------------------------------------------------


def to_numpy(A: MatrixQ) -> np.ndarray:
    return np.array([[float(x) for x in row] for row in A], dtype=float)


def complete_orthogonal(A: np.ndarray) -> np.ndarray:
    """Complete a ``k×n`` Stiefel frame to an ``n×n`` rotation (``det = +1``).

    The first ``k`` rows of the result equal ``A`` up to floating-point error
    when ``A Aᵀ ≈ I``. Extra rows are an orthonormal basis of ``ker(A)``.
    """
    k, n = A.shape
    if k > n:
        raise CertificationError("need k ≤ n to complete to an orthogonal matrix")
    Q = np.zeros((n, n), dtype=float)
    Q[:k] = A
    if k < n:
        _, _, vh = np.linalg.svd(A, full_matrices=True)
        N = vh[k:].copy()
        for i in range(n - k):
            v = N[i]
            for r in range(k):
                v = v - np.dot(Q[r], v) * Q[r]
            for j in range(i):
                v = v - np.dot(Q[k + j], v) * Q[k + j]
            nrm = np.linalg.norm(v)
            if nrm < 1e-18:
                raise CertificationError("failed to complete to an ONB")
            Q[k + i] = v / nrm
    if np.linalg.det(Q) < 0:
        Q[-1] *= -1
    return Q


def _sign_diag_for_cayley(Q: np.ndarray) -> np.ndarray:
    """Diagonal ``±1`` left factor making ``I + D Q`` as well-conditioned as we can."""
    n = Q.shape[0]
    greedy = np.array([1.0 if Q[i, i] >= 0 else -1.0 for i in range(n)])
    candidates = [np.ones(n), greedy, -greedy]
    best = candidates[0]
    best_sv = -1.0
    for d in candidates:
        DQ = (d[:, None]) * Q
        svmin = float(np.linalg.svd(np.eye(n) + DQ, compute_uv=False).min())
        if svmin > best_sv:
            best_sv = svmin
            best = d
    return best


def _prepare_numeric_frame(B: np.ndarray) -> np.ndarray:
    """Row-orthonormalize a free generator if it is not already Stiefel."""
    k, _n = B.shape
    gram = B @ B.T
    if np.allclose(gram, np.eye(k), atol=1e-10):
        return B
    return row_orthonormalize(B)


def reparametrize_cayley(B: np.ndarray, denominator: int = 10_000) -> MatrixQ:
    """Numeric ``k×n`` (Stiefel or free) → rational Stiefel via n×n Cayley.

    Completes ``A`` to ``Q ∈ SO(n)``, left-multiplies by a sign diagonal so
    that inverse Cayley is defined, rationalizes the skew generator with
    coefficient denominator ``D``, and returns the first ``k`` rows of the
    exact rational Cayley transform.
    """
    A = _prepare_numeric_frame(np.asarray(B, dtype=float))
    k, n = A.shape
    Qf = complete_orthogonal(A)
    d = _sign_diag_for_cayley(Qf)
    DQ = (d[:, None]) * Qf
    I = np.eye(n)
    try:
        Sf = (I - DQ) @ np.linalg.inv(I + DQ)
    except np.linalg.LinAlgError as exc:
        raise CertificationError("inverse Cayley failed (I+DQ singular)") from exc
    Sf = 0.5 * (Sf - Sf.T)
    np.fill_diagonal(Sf, 0.0)
    upper: list[Fraction] = []
    for i in range(n):
        for j in range(i + 1, n):
            upper.append(rationalize_coeff(float(Sf[i, j]), denominator))
    S = skew_from_upper(n, upper)
    Q = cayley(S)
    D = [[Fraction(int(d[i]) if i == j else 0) for j in range(n)] for i in range(n)]
    Q = matmul(D, Q)
    return [row[:] for row in Q[:k]]


def reparametrize_givens(B: np.ndarray, max_den: int = 10_000) -> MatrixQ:
    """Numeric ``k×n`` → rational Stiefel by Givens QR of ``Bᵀ``.

    Each plane rotation is replaced by a nearby Pythagorean (rational)
    point on the circle, so the accumulated ``Q`` is exactly orthogonal
    over ``ℚ``. The thin factor is a rational row-orthonormal frame.
    """
    A = _prepare_numeric_frame(np.asarray(B, dtype=float))
    k, n = A.shape
    R: MatrixQ = matrix_q(A.T.tolist())  # n × k
    Q = eye(n)
    for col in range(k):
        for row in range(n - 1, col, -1):
            a = float(R[row - 1][col])
            b = float(R[row][col])
            if abs(a) < 1e-18 and abs(b) < 1e-18:
                continue
            c, s = nearest_pythagorean(a, b, max_den=max_den)
            apply_givens_rows(R, row - 1, row, c, s)
            apply_givens_rows(Q, row - 1, row, c, s)
    # R_final = Q_final @ A.T with Q_final orthogonal, so A.T = Q_final.T @ R
    # and the thin Stiefel factor is the first k rows of Q_final.
    return [row[:] for row in Q[:k]]


def reparametrize(
    B: np.ndarray,
    *,
    method: str = "cayley",
    denominator: int = 10_000,
) -> MatrixQ:
    """Dispatch: ``method`` is ``"cayley"`` or ``"givens"``."""
    if method == "cayley":
        return reparametrize_cayley(B, denominator=denominator)
    if method == "givens":
        return reparametrize_givens(B, max_den=denominator)
    raise CertificationError(f"unknown reparametrization method {method!r}")


# ---------------------------------------------------------------------------
# CPQR pivot margins and inverse-norm test vector
# ---------------------------------------------------------------------------


def pivot_certificate(A: MatrixQ) -> tuple[list[int], list[tuple[int, int, Fraction]], list[Fraction]]:
    """Replay CPQR, recording ``(step, pivot, margin)`` and chosen residuals.

    ``margin`` is ``best − second_best`` among unused columns (or ``best``
    itself when only one column remains). A unique maximizer iff every
    margin is strictly positive.
    """
    k, n = len(A), len(A[0])
    chosen: list[int] = []
    margins: list[tuple[int, int, Fraction]] = []
    residuals_chosen: list[Fraction] = []
    for step in range(k):
        unused = [j for j in range(n) if j not in chosen]
        if not unused:
            break
        res = {j: residual_sq(A, chosen, j) for j in unused}
        best = max(res.values())
        pivot = min(j for j in unused if res[j] == best)
        others = [res[j] for j in unused if j != pivot]
        margin = best - max(others) if others else best
        margins.append((step, pivot, margin))
        residuals_chosen.append(best)
        chosen.append(pivot)
    return chosen, margins, residuals_chosen


def _rayleigh_ok(AJ: MatrixQ, x: Sequence[Fraction], c: int) -> bool:
    if all(v == 0 for v in x):
        return False
    return c * norm_sq(matvec(AJ, x)) < norm_sq(x)


def rationalize_singular_vector(AJ: MatrixQ, max_den: int = 1_000_000) -> VecQ:
    """Rationalize the tiny right singular vector of ``A_J`` (no inequality yet)."""
    Af = to_numpy(AJ)
    _u, _s, vh = np.linalg.svd(Af, full_matrices=True)
    v = vh[-1]
    dens = [max_den, 1_000_000, 250_000, 100_000, 10_000, 1_000, 250]
    seen: set[int] = set()
    best: VecQ | None = None
    best_ratio = 0.0
    for D in dens:
        if D in seen or D <= 0:
            continue
        seen.add(D)
        candidates = [
            [Fraction(float(vi)).limit_denominator(D) for vi in v],
            [Fraction(round(float(vi) * D), D) for vi in v],
        ]
        for x in candidates:
            if all(t == 0 for t in x):
                continue
            ax2 = norm_sq(matvec(AJ, x))
            x2 = norm_sq(x)
            if ax2 == 0:
                return x
            ratio = float(x2 / ax2)
            if ratio > best_ratio:
                best_ratio = ratio
                best = x
    if best is None:
        raise CertificationError("failed to rationalize the tiny singular vector")
    return best


def largest_strict_c(AJ: MatrixQ, x: Sequence[Fraction]) -> int:
    """Largest integer ``c`` with ``c · ‖A_J x‖² < ‖x‖²`` (0 if none)."""
    ax2 = norm_sq(matvec(AJ, x))
    x2 = norm_sq(x)
    if all(v == 0 for v in x):
        return 0
    if ax2 == 0:
        return 10**9
    ratio = x2 / ax2
    c = int(ratio)  # floor
    if Fraction(c) * ax2 >= x2:
        c -= 1
    return max(c, 0)


def inverse_norm_test_vector(
    AJ: MatrixQ,
    c: int,
    max_den: int = 1_000_000,
) -> VecQ:
    """Rational right-vector with ``c · ‖A_J x‖² < ‖x‖²``, from the tiny SVD mode."""
    x = rationalize_singular_vector(AJ, max_den=max_den)
    if _rayleigh_ok(AJ, x, c):
        return x
    ax2 = norm_sq(matvec(AJ, x))
    sig = math.sqrt(float(ax2 / norm_sq(x))) if norm_sq(x) else float("nan")
    raise CertificationError(
        f"no rational test vector with {c}·‖A_J x‖² < ‖x‖² "
        f"(σ_min≈{sig:.6g}; try a larger max_den or a smaller c)"
    )


def selected_square(A: MatrixQ, J: Sequence[int]) -> MatrixQ:
    cols = list(J)
    return [[A[i][j] for j in cols] for i in range(len(A))]


# ---------------------------------------------------------------------------
# Certificate record
# ---------------------------------------------------------------------------


def _frac_str(x: Fraction) -> str:
    return str(x)


def lean_rat(x: Fraction) -> str:
    """Lean ``ℚ`` literal matching the ``frame38`` style in ``SmallInstanceChecks``."""
    if x < 0:
        return f"(-({-x.numerator} : ℚ) / {x.denominator})"
    return f"(({x.numerator} : ℚ) / {x.denominator})"


@dataclass
class Certificate:
    """SPEC §9 certificate. ``ok`` means orthonormal + unique pivots + inv-norm inequality."""

    ok: bool
    k: int
    n: int
    A: MatrixQ
    trajectory: list[int]
    J: list[int]
    margins: list[tuple[int, int, Fraction]]
    min_margin: Fraction
    pivot_residuals: list[Fraction]
    test_vector: VecQ
    c: int
    inv_lb: float
    r_lb: float
    det_AJ: Fraction
    named_poly: float
    below_named_poly: bool
    method: str
    denominator: int | None = None
    tag: str = ""
    note: str = ""
    failures: list[str] = field(default_factory=list)

    def to_json_obj(self) -> dict:
        return {
            "k": self.k,
            "n": self.n,
            "method": self.method,
            "cayley_denominator": self.denominator,
            "certificate": {
                "tag": self.tag,
                "ok": self.ok,
                "J": self.J,
                "trajectory": self.trajectory,
                "min_margin": _frac_str(self.min_margin),
                "min_margin_float": float(self.min_margin),
                "inv_lb": self.inv_lb,
                "r_lb": self.r_lb,
                "c": self.c,
                "pivot_residuals": [_frac_str(x) for x in self.pivot_residuals],
                "margins": [
                    [step, piv, _frac_str(m)] for step, piv, m in self.margins
                ],
                "maxden": max_denominator(self.A),
                "det_AJ": _frac_str(self.det_AJ),
                "named_poly": self.named_poly,
                "below_named_poly": self.below_named_poly,
            },
            "witness_Q": [[_frac_str(x) for x in row] for row in self.A],
            "test_vector_Q": [_frac_str(x) for x in self.test_vector],
            "note": self.note,
            "failures": self.failures,
        }

    def to_json(self, **kwargs) -> str:
        return json.dumps(self.to_json_obj(), indent=1, **kwargs)

    def lean_snippets(self, name: str = "frame") -> str:
        """Optional ``native_decide`` block for ``SmallInstanceChecks.lean``.

        These theorems are witnesses, not public structural results. Do not
        export them from ``Theorems.lean``.
        """
        k, n = self.k, self.n
        rows_lean = []
        for row in self.A:
            rows_lean.append(", ".join(lean_rat(x) for x in row))
        matrix_body = ";\n    ".join(rows_lean)
        vec_body = ", ".join(lean_rat(x) for x in self.test_vector)
        J_set = ", ".join(str(j) for j in sorted(self.J))
        aj_terms = " +\n         ".join(
            f"{name} i {j} * {name}TestVec {p}" for p, j in enumerate(self.trajectory)
        )
        e_note = (
            "Milestone E remains OPEN: a C = 1 witness is not a "
            "polynomial-bound refutation unless the inverse-norm lower "
            "bound exceeds max(n^3, k^3, (k(n-k+1))^2)."
        )
        return f"""/-- Generated SPEC §9 witness. {e_note} -/
def {name} : Matrix (Fin {k}) (Fin {n}) ℚ :=
  !![
    {matrix_body}]

theorem {name}_mul_transpose :
    {name} * {name}ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> native_decide

theorem {name}_cpqr_set :
    cpqrSet {name} = ({{{J_set}}} : Finset (Fin {n})) := by
  native_decide

private def {name}TestVec : Fin {k} → ℚ :=
  ![{vec_body}]

theorem {name}_inv_norm_lb :
    ({self.c} : ℚ) * (∑ i : Fin {k},
        ({aj_terms}) ^ 2) <
      ∑ i : Fin {k}, {name}TestVec i ^ 2 := by
  native_decide
"""


def certify(
    A: MatrixQ | np.ndarray | Sequence[Sequence[Fraction | int | str | float]],
    *,
    c: int | None = None,
    test_vector: Sequence[Fraction | int | str | float] | None = None,
    reparametrize_method: str | None = None,
    denominator: int = 10_000,
    test_vector_den: int = 1_000_000,
    tag: str = "",
    note: str = "",
) -> Certificate:
    """Run SPEC §9 steps 3–5 (and emit data for step 6).

    Parameters
    ----------
    A:
        A ``k×n`` matrix. If it is already a rational frame with ``AAᵀ = I``,
        it is certified as-is. Otherwise it is treated as numeric (or a free
        generator) and re-parametrized.
    c:
        Integer in ``c · ‖A_J x‖² < ‖x‖²``. If omitted, use the workshop
        ``k(n-k+1)`` when the test vector proves it (certifying
        ``r_CPQR > 1``); otherwise the largest integer the vector proves.
    test_vector:
        Optional rational vector in the selected-column coordinates. If
        omitted, the tiny right singular vector is rationalized.
    reparametrize_method:
        ``None`` (auto), ``"exact"`` (require ``AAᵀ = I`` already),
        ``"cayley"``, or ``"givens"``.
    denominator:
        Cayley coefficient denominator ``D``, or Givens ``max_den``.
    """
    method_used = "exact"
    denom_used: int | None = None
    failures: list[str] = []

    if isinstance(A, np.ndarray):
        A_in: MatrixQ | None = None
        A_num = np.asarray(A, dtype=float)
    else:
        A_in = matrix_q(A)
        A_num = to_numpy(A_in)

    if reparametrize_method == "exact":
        if A_in is None:
            raise CertificationError("exact certification needs a rational matrix")
        A_q = A_in
        method_used = "exact"
    elif reparametrize_method in ("cayley", "givens"):
        A_q = reparametrize(
            A_num, method=reparametrize_method, denominator=denominator
        )
        method_used = reparametrize_method
        denom_used = denominator
    elif A_in is not None and is_row_orthonormal(A_in):
        A_q = A_in
        method_used = "exact"
    else:
        A_q = reparametrize_cayley(A_num, denominator=denominator)
        method_used = "cayley"
        denom_used = denominator

    k, n = len(A_q), len(A_q[0])
    ortho = is_row_orthonormal(A_q)
    if not ortho:
        failures.append("AAᵀ ≠ I")

    traj, margins, pivot_residuals = pivot_certificate(A_q)
    min_margin = min((m for _s, _p, m in margins), default=Fraction(0))
    unique = bool(margins) and all(m > 0 for _s, _p, m in margins)
    if not unique:
        failures.append("a CPQR pivot margin is not strictly positive")

    J_sorted = sorted(traj)
    # Prefer the greedy trajectory as the selected block (column order of A_J).
    J_for_block = traj if len(traj) == k else J_sorted
    AJ = selected_square(A_q, J_for_block)
    try:
        det_AJ = det(AJ)
    except Exception as exc:  # pragma: no cover - det is total on square lists
        det_AJ = Fraction(0)
        failures.append(f"det(A_J) failed: {exc}")

    x: VecQ = []
    inv_lb = 0.0
    r_lb = 0.0
    inv_ok = False
    if test_vector is not None:
        x = [to_fraction(v) for v in test_vector]
    else:
        try:
            x = rationalize_singular_vector(AJ, max_den=test_vector_den)
        except CertificationError as exc:
            failures.append(str(exc))
            x = [Fraction(1)] + [Fraction(0)] * (k - 1)

    c_ws = workshop_c(k, n)
    c_max = largest_strict_c(AJ, x) if x else 0
    if c is None:
        c_use = c_ws if c_max >= c_ws else c_max
    else:
        c_use = int(c)
    inv_ok = c_use >= 1 and _rayleigh_ok(AJ, x, c_use)
    if not inv_ok:
        failures.append(
            f"test vector does not prove {c_use}·‖A_J x‖² < ‖x‖² "
            f"(largest feasible c is {c_max})"
        )

    if x and not all(v == 0 for v in x):
        ax2 = norm_sq(matvec(AJ, x))
        x2 = norm_sq(x)
        if ax2 > 0:
            inv_lb = math.sqrt(float(x2 / ax2))
            scale = math.sqrt(c_ws)
            r_lb = inv_lb / scale
        elif x2 > 0:
            inv_lb = float("inf")
            r_lb = float("inf")

    poly = named_poly_scale(k, n)
    below = inv_lb < poly
    ok = ortho and unique and inv_ok
    tag_use = tag or (f"D={denominator}" if denom_used else method_used)
    if not note:
        note = (
            "SPEC §9 certificate. "
            + (
                f"Certified r_CPQR ≥ {r_lb:.6g} > 1 (C = 1 case). "
                if r_lb > 1
                else f"Inverse-norm lower bound r_lb = {r_lb:.6g}. "
            )
            + (
                f"inv_lb ≈ {inv_lb:.6g} is below the named polynomial "
                f"{poly:g}, so Milestone E stays OPEN."
                if below
                else f"inv_lb ≈ {inv_lb:.6g} meets or exceeds the named polynomial "
                f"{poly:g}; Lean formalization is still required before any "
                "polynomial-bound claim. Milestone E stays OPEN until that lands."
            )
        )

    return Certificate(
        ok=ok,
        k=k,
        n=n,
        A=A_q,
        trajectory=traj,
        J=J_sorted,
        margins=margins,
        min_margin=min_margin,
        pivot_residuals=pivot_residuals,
        test_vector=x,
        c=c_use,
        inv_lb=inv_lb,
        r_lb=r_lb,
        det_AJ=det_AJ,
        named_poly=poly,
        below_named_poly=below,
        method=method_used,
        denominator=denom_used,
        tag=tag_use,
        note=note,
        failures=failures,
    )


def certify_json_record(
    path: str | bytes,
    *,
    use_recorded_test_vector: bool = True,
) -> Certificate:
    """Re-certify a JSON record with ``witness_Q`` (and optional ``test_vector_Q``)."""
    rec = json.loads(Path(path).read_text(encoding="utf-8"))
    A = matrix_q(rec["witness_Q"])
    tv = rec.get("test_vector_Q") if use_recorded_test_vector else None
    k, n = rec.get("k", len(A)), rec.get("n", len(A[0]))
    c = workshop_c(int(k), int(n))
    return certify(
        A,
        c=c,
        test_vector=tv,
        reparametrize_method="exact",
        tag=rec.get("certificate", {}).get("tag", "json"),
        note=rec.get("note", ""),
    )


def lean_matrix_def(A: MatrixQ, name: str, k: int | None = None, n: int | None = None) -> str:
    """Just the ``def`` line for a rational frame (helper for generators)."""
    k = len(A) if k is None else k
    n = len(A[0]) if n is None else n
    rows_lean = [", ".join(lean_rat(x) for x in row) for row in A]
    body = ";\n    ".join(rows_lean)
    return f"def {name} : Matrix (Fin {k}) (Fin {n}) ℚ :=\n  !![\n    {body}]"
