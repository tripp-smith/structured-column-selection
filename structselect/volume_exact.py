"""Bounded exact verification of actual volume-weighted inverse expectation.

This enumerates subsets; it is not the efficient sampler required by SPEC §5.
Only rational inputs are accepted. LDLᵀ and solves avoid explicit inverses.
"""
from fractions import Fraction
from itertools import combinations
from math import comb


def _ldl(matrix):
    k = len(matrix)
    lower = [[Fraction(i == j) for j in range(k)] for i in range(k)]
    diagonal = []
    for j in range(k):
        d = matrix[j][j] - sum(
            (lower[j][l] ** 2 * diagonal[l] for l in range(j)), Fraction())
        if d <= 0:
            return None
        diagonal.append(d)
        for i in range(j + 1, k):
            lower[i][j] = (matrix[i][j] - sum(
                (lower[i][l] * lower[j][l] * diagonal[l] for l in range(j)),
                Fraction())) / d
    return lower, diagonal


def _trace_from_factor(lower, diagonal):
    k = len(diagonal)
    trace = Fraction()
    for j in range(k):
        # M x=e_j via L y=e_j, D z=y, Lᵀ x=z.
        y = []
        for i in range(k):
            y.append(Fraction(i == j) - sum(
                (lower[i][l] * y[l] for l in range(i)), Fraction()))
        z = [y[i] / diagonal[i] for i in range(k)]
        x = [Fraction() for _ in range(k)]
        for i in reversed(range(k)):
            x[i] = z[i] - sum(
                (lower[l][i] * x[l] for l in range(i + 1, k)), Fraction())
        trace += x[j]
    return trace


def exact_volume_expectation(rows, *, max_subsets=10000):
    """Return a fully enumerated rational expectation, or explicit exhaustion.

    A nonempty rational Parseval frame is required. No rounding, randomness,
    inverse construction, or partial-result-as-success path is used.
    """
    if not isinstance(max_subsets, int) or max_subsets < 0:
        raise ValueError("max_subsets must be a nonnegative integer")
    if not rows or not rows[0] or any(len(r) != len(rows[0]) for r in rows):
        raise ValueError("expected a nonempty rectangular frame")
    if any(not isinstance(v, (int, str, Fraction)) for row in rows for v in row):
        raise ValueError("exact rational inputs required; floats are not accepted")
    a = [[Fraction(v) for v in row] for row in rows]
    k, n = len(a), len(a[0])
    if any(sum(a[i][l] * a[j][l] for l in range(n)) != int(i == j)
           for i in range(k) for j in range(k)):
        raise ValueError("frame does not satisfy AA^T=I exactly")
    required = comb(n, k)
    if required > max_subsets:
        return {"status": "budget_exhausted", "certified": False,
                "required_subsets": required, "evaluated_subsets": 0}
    terms = []
    expectation = total_mass = Fraction()
    for subset in combinations(range(n), k):
        gram = [[sum(a[i][l] * a[j][l] for l in subset)
                 for j in range(k)] for i in range(k)]
        factor = _ldl(gram)
        if factor is None:
            terms.append({"subset": subset, "weight": Fraction(),
                          "inverse_trace": None})
            continue
        lower, diagonal = factor
        weight = Fraction(1)
        for d in diagonal:
            weight *= d
        trace = _trace_from_factor(lower, diagonal)
        terms.append({"subset": subset, "weight": weight, "inverse_trace": trace})
        expectation += weight * trace
        total_mass += weight
    bound = Fraction(k * (n - k + 1))
    if total_mass != 1 or expectation > bound:
        raise ArithmeticError("exact normalization/expectation verification failed")
    return {"status": "exhaustive_exact", "certified": True,
            "required_subsets": required, "evaluated_subsets": required,
            "total_mass": total_mass, "expectation": expectation,
            "bound": bound, "terms": terms,
            "conditioning": "exact_arithmetic_no_roundoff_estimate"}
