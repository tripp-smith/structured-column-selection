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

## Thread 3 — Milestone C (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneC_adjugate_sum` | `∑_{#J=k} adj(A_J A_Jᵀ) = (n+1-k) adj(AAᵀ)` | `InverseGramExpectation.lean` | `frame23_inverse_gram_sum` |
| `milestoneC_inverse_gram_expectation` | `AAᵀ = I ⇒ ∑ adj(A_J A_Jᵀ) = (n+1-k) I` | `InverseGramExpectation.lean` | same, plus `tests/test_inverse_gram.py` |

The boxed SPEC formula is formalized with adjugates. That matches
`det² • inverse` on invertible column sets and keeps the singular
summands.

Non-claims (intentional):

- no high-probability RRQR bound
- no CPQR statement
- no claim that Problem 4.1 is solved
- Python is a witness, not a source of truth

## Thread 4 — Milestone D (open)

Target:

- `E ‖A_J⁻¹‖_F² = k(n-k+1)` as a thin wrapper around Milestone C
- Markov high-probability bound
  `Pr[ ‖A_J⁻¹‖_2 ≤ √(k(n-k+1)/δ) ] ≥ 1-δ`

Keep the probability layer finite (weighted sums over `Finset (Fin n)`).
