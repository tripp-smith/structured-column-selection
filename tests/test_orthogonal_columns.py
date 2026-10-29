"""CPQR on a partial permutation with pairwise orthogonal columns.

The 2×4 frame has column dots zero off the diagonal and energies
1, 1, 0, 0. Both the max-residual score and the zero-coefficient
increment score pick columns {0, 1}. The Gram is the identity, so
the inverse trace is 2, which is at most k(n-k+1) = 6. This
recomputes the dots from the entries. It is not the theorem.
"""

from fractions import Fraction as F


def test_partial_permutation_cpqr_bound():
    columns = [
        [F(1), F(0)],
        [F(0), F(1)],
        [F(0), F(0)],
        [F(0), F(0)],
    ]

    def dot(left, right):
        return left[0] * right[0] + left[1] * right[1]

    for i in range(4):
        for j in range(4):
            expected = F(1) if i == j and i < 2 else F(0)
            assert dot(columns[i], columns[j]) == expected

    energies = [dot(column, column) for column in columns]
    assert energies == [F(1), F(1), F(0), F(0)]
    first = min(range(4), key=lambda j: (-energies[j], j))
    assert first == 0

    def residual(j):
        coeff = dot(columns[0], columns[j]) / energies[0]
        return energies[j] - coeff * coeff

    residuals = [residual(j) for j in range(1, 4)]
    assert residuals == [F(1), F(0), F(0)]
    second = min(range(1, 4), key=lambda j: (-residual(j), j))
    assert second == 1

    selected = {first, second}
    assert selected == {0, 1}
    gram_trace = sum(dot(columns[j], columns[j]) for j in selected)
    assert gram_trace == 2
    k, n = 2, 4
    assert gram_trace <= k * (n - k + 1)
