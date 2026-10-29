"""Equal column energy at k = 3, on the 3×3 identity.

The closed form 5n - 12 + 6/n equals 5 when n = 3. The identity inverse
trace is 3, and image energy equals coefficient energy. This arithmetic
does not call repository CPQR. It is not the theorem.
"""

from fractions import Fraction as F


def bound(n):
    n = F(n)
    return 5 * n - 12 + 6 / n


def phase_t_bound(n):
    n = F(n)
    k = F(3)
    return (
        2 * (n - 1) / (k - 1)
        + (1 + (2 * k * (n - 1)) / (n * (k - 1))) * ((n - 2) / (k - 2))
    )


def test_k3_bound_matches_prefix_and_identity():
    assert bound(3) == phase_t_bound(3) == 5
    assert bound(6) == phase_t_bound(6)
    cols = [(F(1), F(0), F(0)), (F(0), F(1), F(0)), (F(0), F(0), F(1))]
    assert all(sum(x * x for x in col) == 1 for col in cols)
    assert sum(cols[j][0] * cols[j][0] for j in range(3)) == 1
    x = (F(1), F(0), F(0))
    image = tuple(sum(x[j] * cols[j][i] for j in range(3)) for i in range(3))
    vec = sum(t * t for t in x)
    image_energy = sum(t * t for t in image)
    assert vec == image_energy == 1
    assert vec <= image_energy * bound(3)
