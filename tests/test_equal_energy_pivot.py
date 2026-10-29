"""Equal column energy, second pivot, on a rational 2×4 Hadamard frame.

Rows are orthonormal and every column energy is 1/2. Both pivot scores
select column 0, then column 1. The two-column inverse trace is 4, and
2 (n - 1) / (k - 1) = 6. This arithmetic does not call repository CPQR.
It is not the theorem.
"""

from fractions import Fraction as F


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def test_equal_energy_second_pivot():
    scale = F(1, 2)
    cols = [
        (scale, scale),
        (scale, -scale),
        (scale, scale),
        (scale, -scale),
    ]
    assert dot(cols[0], cols[0]) == F(1, 2)
    assert all(dot(c, c) == F(1, 2) for c in cols)
    assert dot((cols[0][0], cols[1][0], cols[2][0], cols[3][0]),
               (cols[0][0], cols[1][0], cols[2][0], cols[3][0])) == 1
    assert dot((cols[0][1], cols[1][1], cols[2][1], cols[3][1]),
               (cols[0][1], cols[1][1], cols[2][1], cols[3][1])) == 1
    assert dot((cols[0][0], cols[1][0], cols[2][0], cols[3][0]),
               (cols[0][1], cols[1][1], cols[2][1], cols[3][1])) == 0
    e = F(1, 2)
    residuals = []
    for j in range(1, 4):
        inner = dot(cols[0], cols[j])
        residuals.append(e - inner * inner / e)
    assert residuals == [F(1, 2), F(0), F(1, 2)]
    ratios = [(2 * e - r) / (e * r) for r in residuals if r > 0]
    assert ratios == [2, 2]
    assert min(i for i, r in enumerate(residuals, start=1) if r == max(residuals)) == 1
    gram_inv_trace = 2 + 2
    assert gram_inv_trace == 4
    assert gram_inv_trace <= 2 * (4 - 1) / (2 - 1)
