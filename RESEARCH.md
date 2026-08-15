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

- no high-probability RRQR bound in Phase 3
- no CPQR statement
- no claim that Problem 4.1 is solved
- Python is a witness, not a source of truth

## Thread 4 — Milestone D (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneD_expected_inv_frob_sq` | `AAᵀ = I ⇒ ∑ tr(adj(A_J A_Jᵀ)) = k(n-k+1)` | `InverseNormBounds.lean` | `frame23_expected_inv_frob` |
| `milestoneD_markov_inv_frob` | volume mass of `{δ tr(adj) > k(n-k+1) w}` is `≤ δ` | `InverseNormBounds.lean` | same, plus `tests/test_inverse_norm.py` |

The expectation is the trace of the Milestone C identity. The tail is a
finite Markov inequality on those traces; it is the Theorem R1
high-probability bound with `‖·‖_F` in place of `‖·‖_2` (which is
stronger on the invertible locus).

Non-claims (intentional):

- no measure-theoretic probability space
- no CPQR statement
- no CSSP bridge
- no claim that Problem 4.1 is solved
- Python is a witness, not a source of truth

## Thread 5 — Milestone E discovery (in progress)

Delivery so far:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_residual_empty` | empty residual is column energy `∑_i A_{ij}²` | `ColumnPivotedQR.lean` | `tests/test_cpqr.py` leverages |
| `milestoneE_cpqr_card_le` | `#(cpqrSet A) ≤ k` | `ColumnPivotedQR.lean` | frame23 / frame12 cardinalities |
| `milestoneE_cpqr_frame23` | CPQR on the `2×3` frame is `{0,2}` | `SmallInstanceChecks.lean` | same, plus `r_CPQR = 5/8` |

Non-claims (intentional):

- no polynomial CPQR inverse-norm bound
- no CPQR counterexample
- no extra static hypothesis (leverage ratio, coherence, …)
- no claim that Problem 4.1 is solved
- Python census is a witness, not a source of truth
