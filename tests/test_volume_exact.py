"""Independent cofactor recertification of LDL/solve volume expectations."""
from fractions import Fraction as F
from itertools import permutations
import json

import pytest

from structselect.volume_exact import exact_volume_expectation


def permutation_det(matrix):
    n = len(matrix)
    total = F()
    for p in permutations(range(n)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i+1, n))
        term = F(sign)
        for i in range(n):
            term *= matrix[i][p[i]]
        total += term
    return total


def independent_terms(a, result):
    k = len(a)
    actual = proxy = F()
    for term in result['terms']:
        gram = [[sum(a[i][j] * a[l][j] for j in term['subset'])
                 for l in range(k)] for i in range(k)]
        determinant = permutation_det(gram)
        adj_trace = sum(permutation_det([
            [gram[r][c] for c in range(k) if c != i]
            for r in range(k) if r != i]) for i in range(k))
        assert determinant == term['weight']
        proxy += adj_trace
        if determinant:
            assert adj_trace / determinant == term['inverse_trace']
            actual += adj_trace
        else:
            assert term['inverse_trace'] is None
    return actual, proxy


@pytest.mark.parametrize('a,expected,bound', [
    ([[F(1), F(0)]], 1, 2),
    ([[F(3,5), F(4,5)]], 2, 2),
    ([[F(1),F(0),F(0)],[F(0),F(3,5),F(4,5)]], 3, 4),
    ([[F(1),F(0)],[F(0),F(1)]], 2, 2),
    ([[F(6,7),F(-2,7),F(-3,7)],[F(-2,7),F(3,7),F(-6,7)]], 4, 4),
    ([[F(int(i == j)) - F((i+1)*(j+1),15) for j in range(4)]
      for i in range(3)], 6, 6),
    ([[F(1),F(0),F(0)],[F(0),F(1),F(0)]], 2, 4),
    ([[F(1),F(0),F(0)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]], 3, 3),
])
def test_actual_expectation_and_independent_proxy(a, expected, bound):
    result = exact_volume_expectation(a)
    assert result['certified']
    assert result['expectation'] == expected
    assert result['bound'] == bound
    assert independent_terms(a, result) == (expected, bound)
    assert json.dumps(result, default=str, sort_keys=True) == json.dumps(
        exact_volume_expectation(a), default=str, sort_keys=True)
    for delta in (F(1,100), F(1,2), F(1), F(2)):
        good_mass = sum(t['weight'] for t in result['terms']
                        if t['inverse_trace'] is not None and
                        t['inverse_trace'] <= bound / delta)
        assert good_mass >= 1 - delta


def test_budget_exhaustion_is_not_certification():
    result = exact_volume_expectation([[F(3,5),F(4,5)]], max_subsets=1)
    assert result == {'status':'budget_exhausted','certified':False,
                      'required_subsets':2,'evaluated_subsets':0}


@pytest.mark.parametrize('rows', [[], [[1],[0,1]], [[1,1]], [[1.0,0.0]]])
def test_invalid_or_inexact_frames_rejected(rows):
    with pytest.raises(ValueError):
        exact_volume_expectation(rows)


def test_tiny_positive_mass_is_not_rounded_to_singular():
    p = 10 ** 80
    a = [[F(p*p - 1, p*p + 1), F(2*p, p*p + 1)]]
    result = exact_volume_expectation(a)
    assert result['expectation'] == 2
    assert all(t['weight'] > 0 and t['inverse_trace'] is not None
               for t in result['terms'])
    assert independent_terms(a, result) == (2, 2)


@pytest.mark.parametrize('budget', [-1, 0.5])
def test_invalid_budgets_rejected(budget):
    with pytest.raises(ValueError):
        exact_volume_expectation([[1]], max_subsets=budget)
