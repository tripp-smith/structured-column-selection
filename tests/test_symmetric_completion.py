"""Symmetric completion identities on rational pairs.

Two rational pairs `(R, C)` with `Cᵀ = C` and `C² = I - R Rᵀ`: a diagonal
pair with `‖R‖_F² = 9/25`, and a rank-one projection pair. The checks are
the inner-product identity `⟨C w, C v⟩ = ⟨w, v⟩ - ⟨Rᵀ w, Rᵀ v⟩`, the energy
sandwich `(1 - ‖R‖_F²) ‖w‖² ≤ ‖C w‖² ≤ ‖w‖²`, and the perturbation bound
`‖(C - I) v‖² ≤ ‖R‖_F⁴ ‖v‖²`. This check does not call the repository
CPQR code, and it is not the theorem.
"""

from fractions import Fraction as F
from itertools import product


def mat_mul(A, B):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def transpose(A):
    return [list(col) for col in zip(*A)]


def mat_vec(A, v):
    return [sum(a * x for a, x in zip(row, v)) for row in A]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def identity(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def frob(A):
    return sum(x * x for row in A for x in row)


PAIRS = [
    (
        [[F(3, 5), F(0)], [F(0), F(0)]],
        [[F(4, 5), F(0)], [F(0), F(1)]],
    ),
    (
        [[F(12, 25), F(4, 5)], [F(16, 25), F(-3, 5)]],
        [[F(27, 125), F(36, 125)], [F(36, 125), F(48, 125)]],
    ),
]

VECTORS = [
    [F(a), F(b)]
    for a, b in product([-2, -1, 0, 1, 3], repeat=2)
]


def test_pairs_are_symmetric_completions():
    for R, C in PAIRS:
        assert transpose(C) == C
        RRt = mat_mul(R, transpose(R))
        CC = mat_mul(C, C)
        total = [[RRt[i][j] + CC[i][j] for j in range(2)] for i in range(2)]
        assert total == identity(2)


def test_inner_product_identity():
    for R, C in PAIRS:
        Rt = transpose(R)
        for w in VECTORS:
            for v in VECTORS:
                lhs = dot(mat_vec(C, w), mat_vec(C, v))
                rhs = dot(w, v) - dot(mat_vec(Rt, w), mat_vec(Rt, v))
                assert lhs == rhs


def test_energy_sandwich_and_perturbation():
    for R, C in PAIRS:
        eps = frob(R)
        Cminus = [[C[i][j] - F(int(i == j)) for j in range(2)] for i in range(2)]
        for w in VECTORS:
            energy = dot(w, w)
            image = mat_vec(C, w)
            image_energy = dot(image, image)
            assert (1 - eps) * energy <= image_energy <= energy
            shift = mat_vec(Cminus, w)
            assert dot(shift, shift) <= eps * eps * energy
