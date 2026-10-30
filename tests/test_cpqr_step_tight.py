"""Exact rational check of the tighter CPQR trace step.

On the 3×3 identity, the length-2 inverse trace is 2. The tight bound
at B = 2, τ = 1, k = n = 3, t = 2 equals 3. The length-3 inverse trace
equals 3. The old bound 2 + (1 + 2) * 1 equals 5, and 3 < 5. This is
not the theorem. The new bound is not claimed sharp in general.
"""

from fractions import Fraction as F

from structselect.cpqr import cpqr_set, det, matmul, selected_cols, transpose


def tight_bound(B, tau, k, n, t):
    return (1 + (tau * k / n) * B) * ((n - t) / (k - t))


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


def test_identity_cpqr_trace_step_tight():
    identity = [
        [F(1), F(0), F(0)],
        [F(0), F(1), F(0)],
        [F(0), F(0), F(1)],
    ]
    prefix = cpqr_set(identity, k=2)
    trace2 = gram_inv_trace(identity, prefix)
    assert trace2 == 2
    bound = tight_bound(F(2), F(1), F(3), F(3), F(2))
    assert bound == 3
    chosen = cpqr_set(identity, k=3)
    trace3 = gram_inv_trace(identity, chosen)
    assert trace3 == 3
    old = F(2) + (1 + F(2)) * F(1)
    assert old == 5
    assert trace3 < old
