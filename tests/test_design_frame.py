"""Design-padded frame with a non-repeating tight design.

A rational `2×2` leading block `R`, a rational completion `C` with
`R Rᵀ + C Cᵀ = I`, and a design `W` made of four rational orthonormal
bases scaled by `1/2`. The frame `[R | C W]` has orthonormal rows, every
filler energy is at most `k ‖w‖²`, and no two filler columns are
parallel. This check does not call the repository CPQR code, and it is
not the theorem.
"""

from fractions import Fraction as F


def mat_mul(A, B):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def transpose(A):
    return [list(col) for col in zip(*A)]


def identity(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


R = [[F(3, 5), F(0)], [F(0), F(0)]]
C = [[F(4, 5), F(0)], [F(0), F(1)]]

BASES = [
    [[F(1), F(0)], [F(0), F(1)]],
    [[F(3, 5), F(4, 5)], [F(4, 5), F(-3, 5)]],
    [[F(5, 13), F(12, 13)], [F(12, 13), F(-5, 13)]],
    [[F(8, 17), F(15, 17)], [F(15, 17), F(-8, 17)]],
]

W = [[F(1, 2) * entry for basis in BASES for entry in basis[r]] for r in range(2)]


def test_completion_and_design_are_tight():
    RRt = mat_mul(R, transpose(R))
    CCt = mat_mul(C, transpose(C))
    total = [[RRt[i][j] + CCt[i][j] for j in range(2)] for i in range(2)]
    assert total == identity(2)
    assert mat_mul(W, transpose(W)) == identity(2)


def test_design_frame_has_orthonormal_rows_and_small_fillers():
    CW = mat_mul(C, W)
    A = [R[i] + CW[i] for i in range(2)]
    assert mat_mul(A, transpose(A)) == identity(2)
    k = 2
    for j in range(len(W[0])):
        w_energy = sum(W[i][j] ** 2 for i in range(2))
        filler_energy = sum(CW[i][j] ** 2 for i in range(2))
        assert filler_energy <= k * w_energy


def test_filler_columns_are_pairwise_non_parallel():
    CW = mat_mul(C, W)
    cols = transpose(CW)
    for a in range(len(cols)):
        for b in range(a + 1, len(cols)):
            det = cols[a][0] * cols[b][1] - cols[a][1] * cols[b][0]
            assert det != 0
