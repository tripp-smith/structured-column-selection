"""Equal energy does not make every selected block agree.

The integer columns

```
(-7, -4, -4, -3, -3, -1)
(-1, -3, -3,  4,  4,  7)
( 0, -5,  5, -5,  5,  0)
```

have row Gram `100 I` and column squared length `50`. Dividing by `10`
makes every column energy `1/2`. Columns `0` and `1` have inner product
`31/100`. The `2×2` inverse then gives residual `625/1539` at column `5`
and increment ratio `321875/98496` at column `3`, and those are the unique
maximum and minimum. Column `5` is orthogonal to column `0`, so `{0, 1}`
is not the two-column CPQR prefix. This check does not call the repository
CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F


COLS = (
    (-7, -1, 0),
    (-4, -3, -5),
    (-4, -3, 5),
    (-3, 4, -5),
    (-3, 4, 5),
    (-1, 7, 0),
)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def test_integer_frame_is_tight_and_equal_energy():
    for i in range(3):
        for j in range(3):
            gram = sum(COLS[t][i] * COLS[t][j] for t in range(6))
            assert gram == (100 if i == j else 0)
    assert [dot(c, c) for c in COLS] == [50] * 6
    assert dot(COLS[0], COLS[1]) == 31
    assert dot(COLS[0], COLS[5]) == 0


def test_block_residual_and_ratio_order():
    energy = F(1, 2)
    inner = F(31, 100)
    det = energy * energy - inner * inner
    inverse = (
        (energy / det, -inner / det),
        (-inner / det, energy / det),
    )
    stats = {}
    for j in range(2, 6):
        w0 = F(dot(COLS[0], COLS[j]), 100)
        w1 = F(dot(COLS[1], COLS[j]), 100)
        g0 = inverse[0][0] * w0 + inverse[0][1] * w1
        g1 = inverse[1][0] * w0 + inverse[1][1] * w1
        quad = w0 * g0 + w1 * g1
        score = g0 * g0 + g1 * g1
        residual = energy - quad
        stats[j] = (residual, (1 + score) / residual)
    assert stats[5][0] == F(625, 1539)
    assert stats[3][1] == F(321875, 98496)
    assert max(stats, key=lambda j: stats[j][0]) == 5
    assert min(stats, key=lambda j: stats[j][1]) == 3
    assert len({stats[j][0] for j in stats}) == 4
    assert len({stats[j][1] for j in stats}) == 4
