"""Independent exact recertification; no floating-point pivot assertions."""
from fractions import Fraction as F

import pytest

from structselect.column_budget import check_column_budget


def test_dense_long_edges():
    for k in range(1, 13):
        # Every strict upper entry is nonzero: goes beyond bidiagonal U.
        u = [[F(1) if i == j else -F(1, j) if i < j else F(0)
              for j in range(k)] for i in range(k)]
        result = check_column_budget(u)
        assert result['budget_satisfied']
        # Independent forward recurrence for S U = I, rather than U x=e_j.
        s = [[F(i == j) for j in range(k)] for i in range(k)]
        for j in range(k):
            for i in range(j):
                s[i][j] = -sum(s[i][l] * u[l][j] for l in range(i, j))
        assert all(sum(s[i][l] * u[l][j] for l in range(k)) == F(i == j)
                   for i in range(k) for j in range(k))
        assert result['solve_column_energies'] == [
            sum(s[i][j] ** 2 for i in range(k)) for j in range(k)]
        assert result['max_abs_solve_entry'] <= 1
        assert all(e <= j + 1 for j, e in
                   enumerate(result['solve_column_energies']))
        assert sum(result['solve_column_energies']) <= F(k * (k + 1), 2)


def test_entrywise_bound_alone_fails():
    u = [[1, -1, -1], [0, 1, -1], [0, 0, 1]]
    result = check_column_budget(u)
    assert result['column_masses'] == [0, 1, 2]
    assert not result['budget_satisfied']
    # Independent exact witness U (2,1,1)^T = e_2.
    x = [2, 1, 1]
    assert [sum(a * b for a, b in zip(row, x)) for row in u] == [0, 0, 1]
    assert result['max_abs_solve_entry'] == 2
    assert result['solve_column_energies'] == [1, 2, 6]


def test_sharp_chain_closed_form():
    for k in range(13):
        u = [[F(i == j) - F(j == i + 1) for j in range(k)]
             for i in range(k)]
        result = check_column_budget(u)
        assert result['budget_satisfied']
        assert result['solve_column_energies'] == list(range(1, k + 1))
        assert sum(result['solve_column_energies']) == F(k * (k + 1), 2)


def test_invalid_inputs():
    for u in ([[1, 2]], [[2]], [[1, 0], [1, 1]]):
        with pytest.raises(ValueError):
            check_column_budget(u)
