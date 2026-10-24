"""Exact independent oracles for reverse sampling; no frequency-based claims."""
from collections import defaultdict
from dataclasses import asdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations
import json
from random import Random

import pytest

from structselect import volume_sample
import structselect.volume_sampling as sampler
from structselect.volume_exact import _ldl


def frame(k, n):
    # First k rows of a rational Householder orthogonal matrix.
    norm_sq = sum((j+1)**2 for j in range(n))
    return [[F(i == j) - F(2*(i+1)*(j+1), norm_sq) for j in range(n)]
            for i in range(k)]


def gram(a, retained):
    return [[sum(a[i][j]*a[l][j] for j in retained)
             for l in range(len(a))] for i in range(len(a))]


def determinant(a):
    total = F()
    for p in permutations(range(len(a))):
        term = F((-1)**sum(p[i] > p[j] for i in range(len(a))
                           for j in range(i+1,len(a))))
        for i in range(len(a)):
            term *= a[i][p[i]]
        total += term
    return total


def deletion_scores(a, retained):
    g = gram(a, retained)
    factor = _ldl(g)
    assert factor is not None
    return [1-sampler._dot([row[j] for row in a],
                          sampler._solve(*factor, [row[j] for row in a]))
            for j in retained]


@pytest.mark.parametrize('k,n', [(1,5),(2,5),(2,6),(3,5)])
def test_exact_all_state_transition_and_endpoint_law(k,n):
    a = frame(k,n)
    states = {tuple(range(n)): F(1)}
    for size in range(n,k,-1):
        next_states = defaultdict(F)
        for retained, mass in states.items():
            current_det = determinant(gram(a,retained))
            scores = deletion_scores(a,retained)
            assert all(0 <= w <= 1 for w in scores)
            assert sum(scores) == size-k
            for j, score in zip(retained,scores):
                child = tuple(i for i in retained if i != j)
                assert score == determinant(gram(a,child))/current_det
                if score:
                    next_states[child] += mass*score/(size-k)
        states = dict(next_states)
    assert sum(states.values()) == 1
    for selected in combinations(range(n),k):
        assert states.get(selected,F()) == determinant(gram(a,selected))


def test_budget_conditioning_does_not_bias_exact_kernel():
    # Propagate all branches, including rejection and explicit failure.
    a, k, n = frame(2,5), 2, 5
    @lru_cache(None)
    def distribution(retained,budget):
        if len(retained) == k:
            return {retained:F(1)}
        if budget == 0:
            return {None:F(1)}
        scores = deletion_scores(a,retained)
        probabilities = [w/(len(retained) if len(retained)>2*k else len(retained)-k)
                         for w in scores]
        out = defaultdict(F)
        if len(retained)>2*k:
            rejection = 1-sum(probabilities)
            for key,mass in distribution(retained,budget-1).items():
                out[key] += rejection*mass
        for j,p in zip(retained,probabilities):
            if p:
                child = tuple(i for i in retained if i != j)
                for key,mass in distribution(child,budget-1).items():
                    out[key] += p*mass
        return dict(out)
    for budget in range(8):
        dist = distribution(tuple(range(n)),budget)
        assert sum(dist.values()) == 1
        success = 1-dist.get(None,F())
        if success:
            for selected in combinations(range(n),k):
                assert dist.get(selected,F())/success == determinant(gram(a,selected))


def test_actual_hybrid_updates_against_independent_determinants(monkeypatch):
    a, k, n = frame(2,9), 2, 9
    retained = list(range(n))
    lower_implementation = sampler._downdate
    draw_implementation = sampler._weighted_index
    calls = []
    dense_calls = []
    def checked_downdate(lower,diagonal,column):
        j = next(i for i in retained if [row[i] for row in a] == column)
        position = retained.index(j)
        fast = len(retained)>2*k
        lower_implementation(lower,diagonal,column)
        if fast:
            retained[position] = retained[-1]
        retained.pop(position)
        actual_gram = gram(a,retained)
        rebuilt = [[sum(lower[i][r]*diagonal[r]*lower[l][r] for r in range(k))
                    for l in range(k)] for i in range(k)]
        assert rebuilt == actual_gram
        assert all(d>0 for d in diagonal)
        calls.append(j)
    def checked_weighted_draw(rng,weights):
        d = determinant(gram(a,retained))
        expected = [determinant(gram(a,[i for i in retained if i != j]))/d
                    for j in retained]
        assert weights == expected
        dense_calls.append(len(retained))
        return draw_implementation(rng,weights)
    monkeypatch.setattr(sampler,'_downdate',checked_downdate)
    monkeypatch.setattr(sampler,'_weighted_index',checked_weighted_draw)
    result = volume_sample(a,seed=31)
    assert result.ok and result.selected == tuple(sorted(retained))
    assert len(calls) == n-k and dense_calls
    assert result.factor_downdates == n-k
    assert result.dense_dimension <= 2*k
    assert result.gram_determinant == determinant(gram(a,result.selected))
    assert {step['mode'] for step in result.deletions} == {'rejection','dense'}
    assert result.solve_count <= result.proposals + 3*k


@pytest.mark.parametrize('a', [
    [[1,0]], [[F(3,5),F(4,5)]], [[F(1,3)]*9],
    [[1,0,0],[0,F(3,5),F(4,5)]], frame(2,5),
    [[F(10**160-1,10**160+1),F(2*10**80,10**160+1)]],
])
def test_seeded_trajectory_recertified_and_repeatable(a):
    a = [[F(v) for v in row] for row in a]
    k,n = len(a),len(a[0])
    for seed in range(5):
        result = volume_sample(a,k,seed=seed)
        assert result.ok and len(result.selected)==k
        assert json.dumps(asdict(result),default=str,sort_keys=True) == json.dumps(
            asdict(volume_sample(a,k,seed=seed)),default=str,sort_keys=True)
        retained = list(range(n))
        det_before = F(1)
        for step in result.deletions:
            retained.remove(step['removed'])
            det_after = determinant(gram(a,retained))
            assert step['determinant_ratio'] == det_after/det_before
            assert step['deletion_probability'] == det_after/(det_before*(len(retained)+1-k))
            assert det_after > 0
            det_before = det_after
        assert tuple(retained) == result.selected
        assert result.gram_determinant == det_before
        selected_gram = gram(a,result.selected)
        cofactor_trace = sum(determinant([
            [selected_gram[i][l] for l in range(k) if l != j]
            for i in range(k) if i != j]) for j in range(k))
        assert result.inverse_trace == cofactor_trace/det_before


def test_failure_and_degenerate_paths():
    a = frame(2,9)
    result = volume_sample(a,seed=0,max_proposals=0)
    assert result.status=='budget_exhausted' and result.selected is None and not result.ok
    # Can fail after a genuine partial reverse trajectory as well.
    result = volume_sample([[F(1,3)]*9],seed=0,max_proposals=2)
    assert result.status=='budget_exhausted' and result.selected is None
    assert len(result.deletions)>0
    assert volume_sample([],n_columns=100,k=0,max_proposals=0).selected==()
    assert volume_sample([[1,0],[0,1]],max_proposals=0).selected==(0,1)


@pytest.mark.parametrize('a,kwargs', [
    ([[1.0,0.0]],{}), ([[1,1]],{}), ([[1],[0,1]],{}),
    ([[1,0]],{'k':2}), ([[1,0]],{'max_proposals':-1}),
    ([[1,0]],{'n_columns':3}), ([],{'n_columns':-1}),
])
def test_invalid_inputs(a,kwargs):
    with pytest.raises(ValueError):
        volume_sample(a,**kwargs)


def test_weighted_draw_never_selects_zero_mass():
    for seed in range(10):
        assert sampler._weighted_index(Random(seed),[F(0),F(1),F(0)]) == 1


def test_cli_exact_replay_and_failure_exit(tmp_path):
    import subprocess
    import sys
    path = tmp_path/'frame.json'
    path.write_text(json.dumps([[str(v) for v in row] for row in frame(2,7)]))
    command = [sys.executable,'-m','structselect',str(path),'--seed','4']
    first = subprocess.run(command,capture_output=True,text=True)
    second = subprocess.run(command,capture_output=True,text=True)
    assert first.returncode==second.returncode==0
    assert first.stdout==second.stdout
    record = json.loads(first.stdout)
    assert record['result']['status']=='success'
    assert record['implementation_sha256'] and record['input_sha256']
    failed = subprocess.run(command+['--max-proposals','0'],capture_output=True,text=True)
    assert failed.returncode==2
    assert json.loads(failed.stdout)['result']['selected'] is None


def test_finite_fast_proposal_mean_bound_independently():
    for k in range(9):
        for n in range(25):
            total = sum((F(s,s-k) for s in range(2*k+1,n+1)),F())
            assert total <= 2*max(n-2*k,0)
