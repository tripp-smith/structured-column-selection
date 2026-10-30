"""Exact rational check of one CPQR trace step.

On the 3×3 identity, the length-2 Gram is I₂ and its inverse trace is 2.
At B = 2, τ = 1, k = 3, n = 3, t = 2 the step bound equals 5. The
length-3 inverse trace is 3, and 3 ≤ 5. This check does not assert
equality. It is not the theorem.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def step_bound(B, tau, k, n, t):
    return B + (1 + (tau * k / n) * B) * ((n - t) / (k - t))


def cofactor_trace(gram):
    size = len(gram)
    total = F(0)
    for i in range(size):
        minor = [
            [gram[r][c] for c in range(size) if c != i]
            for r in range(size)
            if r != i
        ]
        sign = F(1) if (i + i) % 2 == 0 else F(-1)
        total += sign * det(minor)
    return total


def gram_of(A, indices):
    columns = selected_cols(A, indices)
    return matmul(transpose(columns), columns)


def gram_inv_trace(A, indices):
    gram = gram_of(A, indices)
    return cofactor_trace(gram) / det(gram)


def test_identity_cpqr_trace_step():
    identity = [
        [F(1), F(0), F(0)],
        [F(0), F(1), F(0)],
        [F(0), F(0), F(1)],
    ]
    prefix = cpqr_set(identity, k=2)
    assert gram_of(identity, prefix) == [
        [F(1), F(0)],
        [F(0), F(1)],
    ]
    trace2 = gram_inv_trace(identity, prefix)
    assert trace2 == 2
    bound = step_bound(F(2), F(1), F(3), F(3), F(2))
    assert bound == 5
    chosen = cpqr_set(identity, k=3)
    trace3 = gram_inv_trace(identity, chosen)
    assert trace3 == 3
    assert trace3 <= bound
