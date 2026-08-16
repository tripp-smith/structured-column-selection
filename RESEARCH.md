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

## Thread 5 — Milestone E structural CPQR (completed)

Delivery:

| Name | Statement | File | Independent check |
| --- | --- | --- | --- |
| `milestoneE_residual_empty` | empty residual is column energy `∑_i A_{ij}²` | `ColumnPivotedQR.lean` | `tests/test_cpqr.py` leverages |
| `milestoneE_cpqr_card_le` | `#(cpqrSet A) ≤ k` | `ColumnPivotedQR.lean` | frame23 / frame12 cardinalities |
| `milestoneE_leverage_sum` | `AAᵀ = I ⇒ ∑_j residualSq A ∅ j = k` | `ColumnPivotedQR.lean` | frame23 energies `1 + 9/25 + 16/25 = 2` |
| `milestoneE_first_pivot_is_max` | a first pivot maximises empty residual | `ColumnPivotedQR.lean` | frame23 first pivot is column `0` |
| `milestoneE_first_leverage_ge` | a first pivot has leverage `≥ k/n` | `CPQRVolume.lean` | frame23 first leverage `1 ≥ 2/3` |
| `milestoneE_cpqr_card_eq` | `AAᵀ = I ⇒ #(cpqrSet A) = k` | `ColumnPivotedQR.lean` | frame23 / frame12 cardinalities |
| `milestoneE_k1_volume_ge` | `k=1 ⇒ volumeWeight(cpqrSet) ≥ n⁻¹` | `CPQRVolume.lean` | `frame12` volume `16/25 ≥ 1/2` |
| `milestoneE_residual_energy` | `AAᵀ = I`, Gram invertible `⇒ ∑ residualSq = k-#J` | `ResidualEnergy.lean` | frame23 after `{0}`: `0+9/25+16/25=1` |
| `milestoneE_next_residual_ge` | unused max residual `≥ (k-#J)/(n-#J)` | `ResidualEnergy.lean` | frame23 after `{0}`: `16/25 ≥ 1/2` |
| `milestoneE_cpqr_volume_ge_binomial` | `volumeWeight(cpqrSet) ≥ 1/C(n,k)` (not polynomial) | `CPQRVolume.lean` | frame23 `16/25 ≥ 1/3`; frame12 `16/25 ≥ 1/2` |
| `milestoneE_mulVec_energy_le` | `AAᵀ = I ⇒` energy of `A x` is `≤` energy of `x` | `PrefixInverse.lean` | column energies `≤ 1` |
| `milestoneE_col_energy_le` | `AAᵀ = I ⇒` column leverage `≤ 1` | `PrefixInverse.lean` | frame23 leverages `1, 9/25, 16/25` |
| `milestoneE_last_residual_ge` | last CPQR residual `≥ 1/(n-k+1)` | `PrefixInverse.lean` | frame23 last residual `16/25 ≥ 1/2` |

Independent computational witness: `frame23_cpqr_set` selects `{0,2}` with `r_CPQR = 5/8`.

The card identity is a full-rank stopping theorem: CPQR on an
orthogonal-row matrix cannot halt before `k` columns. The `k = 1`
volume bound is a workshop-scale inverse-magnitude theorem for a
single orthonormal row. Residual energy and the binomial volume bound
are identities for every orthogonal-row matrix; `1/C(n,k)` is
exponential in `k` when `n ≈ 2k` and is not a `poly(n,k)` inverse-norm
bound. None of these closes Milestone E.

## Thread 5b — Milestone E characterization census (in progress)

SPEC §8 census contract (not a characterization outcome):

| Artifact | Statement | File | Independent check |
| --- | --- | --- | --- |
| `run_census` | Haar, Hadamard, Fourier, leverage-skew, near-duplicate, Kahan-like frames | `structselect/census.py` | `tests/test_census.py` |
| `experiments/census_seed0.json` | recorded `r_CPQR`, `σ_min`, pivots, optional exhaustive opt | `experiments/` | regenerate with seed 0 |

On the seed-0 sweep the worst recorded ratio is Hadamard `k=3,n=8`
with `r_CPQR = 2/3 < 1`. Several Haar draws are slightly worse than
the exhaustive optimum and still below the workshop scale.

Wave 1 (seed 1): Mercedes-Benz / simplex / Paley / icosahedral ETFs,
clustered near-parallels, Haar `k ≤ 12`, and block-diagonal ETF
copies. Worst recorded `r_CPQR` is `√3/2` on the `2×3` simplex /
Mercedes-Benz frame. No sample exceeded `r = 1` or the named
polynomial yardstick. The simplex saturates `1/C(n,k)` and
`σ_min = |det|` at `n = k+1`; clustered near-parallels do not
survive `row_orthonormalize`. JSON:
`experiments/census_wave1_*_seed1.json`.

This is **not** a polynomial CPQR theorem and **not** a
machine-checked counterexample. Milestone E remains open.

The dated reasoning log, census labels, and ordered next-work queue
are in `CHECKPOINT.md`. Residual energy and the binomial volume bound
are now proved there as non-polynomial theorems.

Non-claims (intentional):

- no polynomial CPQR inverse-norm bound for general `k`
- no CPQR counterexample
- no extra static hypothesis (leverage ratio, coherence, …)
- no claim that Problem 4.1 is solved
- Python census is a witness, not a source of truth
- `milestoneE_k1_volume_ge` does not close Milestone E
- `milestoneE_cpqr_volume_ge_binomial` is exponential, not polynomial,
  and does not close Milestone E
- `milestoneE_mulVec_energy_le`, `milestoneE_col_energy_le`, and
  `milestoneE_last_residual_ge` do not close Milestone E
