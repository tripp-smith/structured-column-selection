# Findings

## Phase 1 (Milestone A) delivered

Working with a `k × n` matrix `A` satisfying `A Aᵀ = I` is equivalent to
working with `Q := Aᵀ` satisfying `Qᵀ Q = I`. Selected `k × k` column
blocks and their Gram matrices are available as Lean definitions.

## Phase 2 (Milestone B) delivered

If `A Aᵀ = I`, the squared maximal minors form a finitely supported
probability distribution on the `k`-subsets of columns:

```text
∑_{|J|=k} det(A_J)² = 1.
```

This is the Cauchy–Binet evaluation of `det(A Aᵀ) = det(I) = 1`. The
identity is proved for a general commutative ring first
(`det(A B) = ∑_{|S|=k} det(A_S) det(B^S)`), then specialised to
`B = Aᵀ` and to orthogonal-row real matrices.

An independent rational check on

```text
A = [ 1  0  0 ]
    [ 0  3/5 4/5 ]
```

enumerates the three 2-subsets and recovers `(3/5)² + (4/5)² + 0 = 1`.
The same arithmetic is repeated outside Lean in
`tests/test_volume_normalization.py`.

## What remains open

The phase does **not** prove the inverse-Gram expectation identity or
the randomized high-probability inverse-norm bound. Those belong to
Milestones C and D. CPQR is untouched.
