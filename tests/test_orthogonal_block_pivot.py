"""Orthogonal equal-energy blocks make the next ratio decrease in the residual.

On the `3×3` identity the block `{0, 1}` is pairwise orthogonal and every
column energy is `1`. The remaining column has residual `1` and increment
ratio `1`, matching `(2e - r) / (e r)`. A separate exact comparison records
that `1 + q / λ_min` at `k = 3`, `n = 6`, and `λ_min = 2/5` sits above the
increment allowance, so that estimate does not finish the induction. Neither
check calls the repository CPQR code, and neither is the theorem.
"""

from fractions import Fraction as F


def test_identity_block_ratio_matches_the_residual_formula():
    energy = F(1)
    residual = F(1)
    score = F(0)
    ratio = (1 + score) / residual
    assert ratio == (2 * energy - residual) / (energy * residual)
    smaller = F(1, 2)
    larger = F(1, 4)
    def formula(r):
        return (2 * energy - r) / (energy * r)
    assert formula(smaller) < formula(larger)


def test_lambda_min_estimate_exceeds_the_increment_allowance():
    k = 3
    n = 6
    energy = F(k, n)
    residual_floor = F(k - 2, n - 2)
    mu = F(2, 5)
    left = 1 + (energy - residual_floor) / mu
    trace = (2 * energy) / (mu * (2 * energy - mu))
    right = (n - 4 + trace) / (n - 2)
    assert left == F(13, 8)
    assert right == F(37, 24)
    assert right < left
