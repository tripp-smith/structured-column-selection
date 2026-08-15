# Research threads

## Thread 1 — Milestone A (completed)

Delivery:

- `milestoneA_transpose_correspondence`
- `milestoneA_selectedSquare_entry`
- `milestoneA_selectedGram_formula`

These establish the first formal contract from `SPEC.md`:
orthogonal-row/orthogonal-column transpose correspondence plus basic
selected-column algebra needed for subsequent determinant and expectation
identities.

## Thread 2 — Milestone B (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneB_cauchyBinet` | `det(AB) = ∑_{#S=k} det(A_S) det(B^S)` | `CauchyBinet.lean` | `frame23` / `frame12` enumerations |
| `milestoneB_volume_normalization` | `AAᵀ = I ⇒ ∑_{#J=k} det(A_J)² = 1` | `VolumeWeights.lean` | same, plus Python `tests/test_volume_normalization.py` |

Non-claims (intentional):

- no inverse-Gram expectation
- no high-probability RRQR bound
- no CPQR statement
- no claim that Problem 4.1 is solved

## Thread 3 — Milestone C (open)

Target:

- finite matrix identity
  `∑_{|J|=k} det(A_J)² (A_J A_Jᵀ)⁻¹ = (n-k+1) I`

This remains the central formal milestone. Keep the argument algebraic
(adjugates, complementary minors) before introducing probability
abstractions.
