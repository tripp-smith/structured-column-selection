"""Exact reverse volume sampling for rational Parseval frames.

A hybrid rejection/small-dense algorithm. LDLᵀ factors, solves and projection
updates are used; the inverse of the frame Gram is never constructed.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from random import Random


@dataclass(frozen=True)
class VolumeSample:
    selected: tuple[int, ...] | None
    status: str
    seed: int
    proposals: int
    deletions: tuple[dict, ...]
    factor_downdates: int
    dense_dimension: int
    solve_count: int
    gram_determinant: Fraction
    inverse_trace: Fraction | None
    certification: str
    conditioning: str = "exact_rational_arithmetic"

    @property
    def ok(self):
        return self.status == "success"


def _frame(rows, n_columns):
    if any(not isinstance(v, (int, str, Fraction)) for row in rows for v in row):
        raise ValueError("exact rational input required; floats are not accepted")
    k = len(rows)
    n = len(rows[0]) if k else (0 if n_columns is None else n_columns)
    if not isinstance(n, int) or n < 0:
        raise ValueError("n_columns must be a nonnegative integer")
    if any(len(row) != n for row in rows) or (n_columns is not None and n_columns != n):
        raise ValueError("inconsistent frame dimensions")
    a = [[Fraction(v) for v in row] for row in rows]
    if any(sum(a[i][j] * a[l][j] for j in range(n)) != int(i == l)
           for i in range(k) for l in range(k)):
        raise ValueError("AA^T must equal I exactly")
    return a, k, n


def _solve(lower, diagonal, rhs):
    k = len(diagonal)
    y = []
    for i in range(k):
        y.append(rhs[i] - sum((lower[i][j] * y[j] for j in range(i)), Fraction()))
    x = [Fraction() for _ in range(k)]
    for i in reversed(range(k)):
        x[i] = y[i] / diagonal[i] - sum(
            (lower[j][i] * x[j] for j in range(i + 1, k)), Fraction())
    return x


def _downdate(lower, diagonal, column):
    """LDLᵀ rank-one downdate in O(k²) rational arithmetic operations."""
    w = list(column)
    alpha = Fraction(-1)
    for j in range(len(diagonal)):
        p = w[j]
        old_d = diagonal[j]
        new_d = old_d + alpha * p * p
        if new_d <= 0:
            raise ArithmeticError("accepted deletion lost positive definiteness")
        beta = alpha * p / new_d
        alpha = alpha * old_d / new_d
        diagonal[j] = new_d
        for i in range(j + 1, len(diagonal)):
            w[i] -= p * lower[i][j]
            lower[i][j] += beta * w[i]


def _dot(x, y):
    return sum((a * b for a, b in zip(x, y)), Fraction())


def _weighted_index(rng, weights):
    denominator = 1
    for w in weights:
        denominator = lcm(denominator, w.denominator)
    integers = [int(w * denominator) for w in weights]
    total = sum(integers)
    if total <= 0 or any(w < 0 for w in integers):
        raise ArithmeticError("invalid deletion weights")
    ticket = rng.randrange(total)
    for i, weight in enumerate(integers):
        if ticket < weight:
            return i
        ticket -= weight
    raise ArithmeticError("unreachable exact weighted draw")


def volume_sample(rows, k=None, *, seed=0, max_proposals=1000000, n_columns=None):
    """Sample k columns without subset enumeration; return explicit failure.

    k must equal the number of orthonormal rows. Success returns a VolumeSample
    with sorted indices and exact deletion evidence. Budget exhaustion has
    selected=None; it is never a purported sample. Fixed inputs/seed/revision
    are deterministic. Arithmetic-operation counts do not bound rational bit
    growth or random-bit complexity. Python random.Random is a seeded source,
    not a cryptographic or formally extracted source of independent uniforms.
    """
    if not isinstance(seed, int) or not isinstance(max_proposals, int) or max_proposals < 0:
        raise ValueError("integer seed and nonnegative proposal budget required")
    a, dimension, n = _frame(rows, n_columns)
    if k is None:
        k = dimension
    if not isinstance(k, int) or k != dimension:
        raise ValueError("sample size must equal the orthonormal row count")
    lower = [[Fraction(i == j) for j in range(k)] for i in range(k)]
    diagonal = [Fraction(1) for _ in range(k)]
    retained = list(range(n))
    rng = Random(seed)
    trajectory = []
    proposals = solves = dense_dimension = 0
    determinant = Fraction(1)

    def result(status):
        nonlocal solves
        inverse_trace = None
        if status == 'success':
            inverse_trace = Fraction()
            for j in range(k):
                inverse_trace += _solve(lower, diagonal,
                    [Fraction(i == j) for i in range(k)])[j]
            solves += k
        return VolumeSample(tuple(sorted(retained)) if status == 'success' else None,
                            status, seed, proposals, tuple(trajectory), len(trajectory),
                            dense_dimension, solves, determinant, inverse_trace,
                            'exact_rational_transitions_and_inverse_trace' if status == 'success'
                            else 'uncertified_budget_exhaustion')

    if k == 0:
        retained = []
        return result('success')

    while len(retained) > 2 * k:
        if proposals >= max_proposals:
            return result('budget_exhausted')
        proposals += 1
        position = rng.randrange(len(retained))
        j = retained[position]
        column = [row[j] for row in a]
        score = 1 - _dot(column, _solve(lower, diagonal, column))
        solves += 1
        if not 0 <= score <= 1:
            raise ArithmeticError("deletion score outside [0,1]")
        if rng.randrange(score.denominator) >= score.numerator:
            continue
        before = len(retained)
        _downdate(lower, diagonal, column)
        determinant *= score
        trajectory.append({'removed':j, 'retained_before':before, 'mode':'rejection',
                           'determinant_ratio':score,
                           'deletion_probability':score / (before-k)})
        retained[position] = retained[-1]
        retained.pop()

    if len(retained) == k:
        return result('success')
    # Only at most 2k columns remain. This is A_Sᵀ G_S^{-1} A_S,
    # a projection Gram, not an explicitly formed inverse of G_S.
    dense_dimension = len(retained)
    columns = [[row[j] for row in a] for j in retained]
    solutions = [_solve(lower, diagonal, column) for column in columns]
    solves += len(columns)
    projection = [[_dot(column, solution) for solution in solutions] for column in columns]
    while len(retained) > k:
        if proposals >= max_proposals:
            return result('budget_exhausted')
        weights = [1 - projection[i][i] for i in range(len(retained))]
        if any(w < 0 or w > 1 for w in weights) or sum(weights) != len(retained)-k:
            raise ArithmeticError("dense deletion normalization failed")
        proposals += 1
        position = _weighted_index(rng, weights)
        score = weights[position]
        j = retained[position]
        before = len(retained)
        _downdate(lower, diagonal, [row[j] for row in a])
        determinant *= score
        trajectory.append({'removed':j, 'retained_before':before, 'mode':'dense',
                           'determinant_ratio':score,
                           'deletion_probability':score / (before-k)})
        keep = [i for i in range(len(retained)) if i != position]
        projection = [[projection[i][l] + projection[i][position] *
                       projection[position][l] / score for l in keep] for i in keep]
        retained.pop(position)
    return result('success')
