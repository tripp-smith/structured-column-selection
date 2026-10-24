"""Exact finite checks for the additional CPQR coefficient-budget hypothesis.

No pivot selection is performed. Inputs are rational unit upper triangular
coefficient matrices, not necessarily factors of a row-orthogonal frame.
"""
from fractions import Fraction


def check_column_budget(rows):
    """Return exact budget diagnostics and triangular-solve inverse energies.

    Invalid inputs raise ValueError. A failed budget is reported as such,
    never as a certified CPQR statement. All loops have the input dimension
    as their explicit bound; there is no search or convergence budget.
    """
    u = [[Fraction(x) for x in row] for row in rows]
    k = len(u)
    if any(len(row) != k for row in u):
        raise ValueError("expected a square matrix")
    if any(u[i][j] != (1 if i == j else 0)
           for i in range(k) for j in range(i + 1)):
        raise ValueError("expected unit upper triangular matrix")
    masses = [sum((abs(u[i][j]) for i in range(j)), Fraction())
              for j in range(k)]
    energies = []
    max_entry = Fraction()
    # Solve U x = e_j one right-hand side at a time; no explicit inverse.
    for j in range(k):
        x = [Fraction() for _ in range(k)]
        for i in reversed(range(k)):
            x[i] = Fraction(i == j) - sum(
                (u[i][l] * x[l] for l in range(i + 1, k)), Fraction())
        energies.append(sum((v * v for v in x), Fraction()))
        max_entry = max(max_entry, *(abs(v) for v in x))
    return {"dimension": k, "column_masses": masses,
            "budget_satisfied": all(m <= 1 for m in masses),
            "solve_column_energies": energies,
            "max_abs_solve_entry": max_entry,
            "stop_reason": "exhaustive_finite_solve",
            "certification": "exact_rational_coefficient_check"}
