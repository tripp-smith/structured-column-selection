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

## Phase 3 (Milestone C) delivered

The finite inverse-Gram identity is

```text
∑_{|J|=k} adj(A_J A_Jᵀ) = (n - k + 1) I
```

when `A Aᵀ = I`. More generally, without orthogonality,

```text
∑_{|J|=k} adj(A_J A_Jᵀ) = (n - k + 1) adj(A Aᵀ).
```

The proof deletes one row, applies Cauchy–Binet to the resulting
`(k-1)×k` and `(k-1)×n` products, and counts how many `k`-sets contain
each `(k-1)`-set (`n-k+1` of them).

The adjugate form is the correct reading of
`∑ det(A_J)² (A_J A_Jᵀ)⁻¹`. Mathlib's matrix inverse is zero on
singular blocks, which would drop nonzero adjugate contributions. On
the running `2×3` witness the singular pair `{1,2}` contributes
`[[1,0],[0,0]]`; omitting it would break the identity.

Independent check on

```text
A = [ 1  0  0 ]
    [ 0  3/5 4/5 ]
```

the three adjugates are `[[9/25,0],[0,1]]`, `[[16/25,0],[0,1]]` and
`[[1,0],[0,0]]`, summing to `2 I`. The same arithmetic is repeated in
`tests/test_inverse_gram.py`.

## What remains open

The randomized high-probability inverse-norm bound (Milestone D) and
all CPQR statements.
