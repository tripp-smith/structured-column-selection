"""Independent determinant and closed-form checks of compressed research frames."""
from fractions import Fraction as F
import json

import pytest

from structselect import wide_cpqr


def determinant(matrix):
    """Exact row elimination, independent of the implementation's LDL solves."""
    a = [list(row) for row in matrix]
    result = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F()
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            result = -result
        result *= a[j][j]
        for i in range(j + 1, len(a)):
            multiplier = a[i][j] / a[j][j]
            for q in range(j + 1, len(a)):
                a[i][q] -= multiplier * a[j][q]
    return result


def gram(columns):
    return [[sum(x * y for x, y in zip(a, b)) for b in columns]
            for a in columns]


def residual(columns, vector):
    """Bordered Gram determinant ratio: no tail/projector formula assumed."""
    return determinant(gram(columns + [vector])) / determinant(gram(columns))


@pytest.mark.parametrize('m', [2, 3])
def test_every_prefix_with_independent_bordered_gram_determinants(m):
    result = wide_cpqr.compressed_certificate(m)
    assert result['certified']
    k = result['k']
    r = result['triangular']
    lower = result['completion_lower']
    weights = result['completion_weights']
    t = result['repetitions']
    columns = [[r[i][j] for i in range(k)] for j in range(k)]
    # Rational pair products represent the algebraic columns exactly.
    for i in range(k):
        for j in range(k):
            completed = sum(r[i][q] * r[j][q] for q in range(k))
            completed += t * sum(lower[i][q] * lower[j][q] * weights[q] / t
                                 for q in range(k))
            assert completed == (i == j)
    margin = result['minimum_pivot_margin']
    assert margin > 0
    for prefix in range(k):
        retained = columns[:prefix]
        pivot = residual(retained, columns[prefix])
        assert pivot == r[prefix][prefix] ** 2
        for j in range(prefix + 1, k):
            actual = residual(retained, columns[j])
            assert actual == sum(r[i][j] ** 2 for i in range(prefix, k))
            assert pivot - actual >= margin
        for q in range(k):
            vector = [lower[i][q] for i in range(k)]
            actual = residual(retained, vector) * weights[q] / t
            assert 0 <= actual <= result['completion_column_energies'][q]
            assert pivot - actual >= margin


@pytest.mark.parametrize('m', [2, 3, 4])
def test_inverse_witness_by_closed_form_and_direct_multiplication(m):
    result = wide_cpqr.compressed_certificate(m)
    k = result['k']
    r = result['triangular']
    c = result['coupling']
    last = r[-1][-1]
    # This formula does not use back-substitution or the LDL factorization.
    closed = [c * (1 + c) ** (k - i - 2) / last for i in range(k - 1)]
    closed.append(1 / last)
    assert closed == result['witness']
    assert [sum(r[i][j] * closed[j] for j in range(k))
            for i in range(k)] == [F(i == k - 1) for i in range(k)]
    assert result['inverse_energy'] == sum(x * x for x in closed)
    assert result['inverse_entry'] >= wide_cpqr.growth_parameters(m)['inverse_lower_candidate']


@pytest.mark.parametrize('m', [2, 3, 4])
def test_closed_form_head_beats_scale_by_cross_multiplication(m):
    """Integer comparison of the closed head with `(2m/3)*(4/3)^(m-1)`.

    This does not build the frame or certify a pivot sequence.
    """
    k = m * m
    head_num = 4 * m * k * (4 * k + 2 * m + 1) ** (k - 2)
    head_den = (4 * k - 1) ** (k - 1)
    # (2m/3)*(4/3)^(m-1) = 2*m*4^(m-1) / 3^m
    scale_num = 2 * m * 4 ** (m - 1)
    scale_den = 3 ** m
    assert head_num * scale_den >= scale_num * head_den
    assert wide_cpqr.growth_parameters(m)['frame_certified'] is False


def test_canonical_result_is_deterministic():
    first = json.dumps(wide_cpqr.compressed_certificate(2), default=str, sort_keys=True)
    second = json.dumps(wide_cpqr.compressed_certificate(2), default=str, sort_keys=True)
    assert first == second


def test_dimension_budget_is_explicit_and_does_not_factor(monkeypatch):
    def forbidden_factor(_):
        raise AssertionError('budget must be checked before matrix work')
    monkeypatch.setattr(wide_cpqr, '_ldl', forbidden_factor)
    result = wide_cpqr.compressed_certificate(3, max_dimension=8)
    assert result == {'status': 'dimension_budget_exhausted', 'certified': False,
                      'm': 3, 'k': 9, 'n': 209961, 'required_dimension': 9}


@pytest.mark.parametrize('m', [0, 1, -1, True, 2.0, F(2), '2'])
def test_invalid_parameters_rejected(m):
    with pytest.raises(ValueError):
        wide_cpqr.compressed_certificate(m)


@pytest.mark.parametrize('budget', [-1, True, 4.0, F(4)])
def test_invalid_budgets_rejected(budget):
    with pytest.raises(ValueError):
        wide_cpqr.compressed_certificate(2, max_dimension=budget)


def test_failed_completion_factor_is_not_certification(monkeypatch):
    monkeypatch.setattr(wide_cpqr, '_ldl', lambda _: None)
    with pytest.raises(ArithmeticError, match='not positive definite'):
        wide_cpqr.compressed_certificate(2)


def test_failed_reconstruction_is_not_certification(monkeypatch):
    monkeypatch.setattr(wide_cpqr, '_ldl', lambda a: (a, [F(1)] * len(a)))
    with pytest.raises(ArithmeticError, match='completion identity failed'):
        wide_cpqr.compressed_certificate(2)


@pytest.mark.parametrize('m', [2, 64, 1024])
def test_large_scalar_checks_do_not_certify_frames(m):
    result = wide_cpqr.growth_parameters(m)
    k, eps, c, alpha, t, n = wide_cpqr.parameters(m)
    assert eps * eps + c * c == 1 - F(12 * m * m, (4 * m * m + 1) ** 2)
    assert result['bernoulli_diagonal_ratio_lower'] == F(2 * k + 1, 4 * k + 1)
    assert t == 32 * k ** 3 and n == k + 32 * k ** 4
    assert alpha == F(1, 2 * k)
    # Integer cross multiplication is independent of the Fraction comparison.
    bound = max(n ** 3, k ** 3, (k * (n - k + 1)) ** 2)
    crosses = 2 * m * 4 ** (m - 1) > bound * 3 ** m
    assert result['exceeds_named_polynomial_if_family_proved'] == crosses
    assert result['frame_certified'] is False
    assert result['status'] == 'exact_scalar_bounds_only'
