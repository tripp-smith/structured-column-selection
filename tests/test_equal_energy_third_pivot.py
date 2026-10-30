"""Equal energy does not make the third CPQR pivot agree.

The integer columns

```
(-3, -2, -2)
(-4, -1,  0)
(-2,  2,  3)
(-2,  3, -2)
(-1,  0,  4)
( 0, -4,  1)
```

have row Gram `34 I` and column squared length `17`. Dividing by `√34`
makes every column energy `1/2`. Both rules take column `0`, then column
`2` (tied with column `3`, least index `2`). After `{0, 2}`, the residual
maximum is column `3` and the increment-ratio minimum is column `5`.
This check does not call the repository CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F


COLS = (
    (-3, -2, -2),
    (-4, -1, 0),
    (-2, 2, 3),
    (-2, 3, -2),
    (-1, 0, 4),
    (0, -4, 1),
)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def test_integer_frame_is_tight_and_equal_energy():
    for i in range(3):
        for j in range(3):
            gram = sum(COLS[t][i] * COLS[t][j] for t in range(6))
            assert gram == (34 if i == j else 0)
    assert [dot(c, c) for c in COLS] == [17] * 6
    assert dot(COLS[0], COLS[2]) == -4


def test_second_and_third_pivot_order():
    energy = F(1, 2)
    single = {}
    for j in range(1, 6):
        inner = F(dot(COLS[0], COLS[j]), 34)
        residual = energy - inner * inner / energy
        ratio = (2 * energy - residual) / (energy * residual)
        single[j] = (residual, ratio)
    assert single[2][0] == single[3][0] == F(273, 578)
    assert single[2][1] == single[3][1] == F(610, 273)
    assert max(single, key=lambda j: (single[j][0], -j)) == 2
    assert min(single, key=lambda j: (single[j][1], j)) == 2
    gram = (
        (energy, F(dot(COLS[0], COLS[2]), 34)),
        (F(dot(COLS[2], COLS[0]), 34), energy),
    )
    det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0]
    inverse = (
        (gram[1][1] / det, -gram[0][1] / det),
        (-gram[1][0] / det, gram[0][0] / det),
    )
    pair = {}
    for j in (1, 3, 4, 5):
        w0 = F(dot(COLS[0], COLS[j]), 34)
        w1 = F(dot(COLS[2], COLS[j]), 34)
        g0 = inverse[0][0] * w0 + inverse[0][1] * w1
        g1 = inverse[1][0] * w0 + inverse[1][1] * w1
        quad = w0 * g0 + w1 * g1
        score = g0 * g0 + g1 * g1
        residual = energy - quad
        pair[j] = (residual, (1 + score) / residual)
    assert pair[3][0] == F(189, 442)
    assert pair[5][1] == F(722279, 262353)
    assert max(pair, key=lambda j: pair[j][0]) == 3
    assert min(pair, key=lambda j: pair[j][1]) == 5
    assert len({pair[j][0] for j in pair}) == 4
    assert len({pair[j][1] for j in pair}) == 4
