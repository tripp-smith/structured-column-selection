---
name: e-characterization
description: >-
  Continue Milestone E characterization: SPEC §8 census, §9
  counterexample protocol, or §10 structural refinement. Use when the
  user asks for a CPQR polynomial bound, a counterexample, r_CPQR
  growth, Haar/Hadamard/Kahan frames, or the remaining E outcomes.
---

# Milestone E characterization

Structural CPQR facts already delivered:

- `milestoneE_leverage_sum`
- `milestoneE_first_pivot_is_max`
- `milestoneE_cpqr_card_eq`

Those do **not** close Milestone E. E still requires one of:

1. a polynomial CPQR theorem for all orthogonal-row matrices;
2. an explicit machine-checked counterexample;
3. a counterexample plus a stronger static class with a poly theorem.

## Required order (SPEC §8)

Do not attempt a general Lean bound before a census.

Families to test:

- Haar/Stiefel frames
- normalized Hadamard and Fourier-type frames
- highly nonuniform leverage frames
- near-duplicate columns compensated to keep `AAᵀ = I`
- orthogonalized variants of known adverse CPQR constructions

For each instance record

```text
r_CPQR = ‖A_J⁻¹‖₂ / √(k(n-k+1))
```

plus `σ_min`, `|det A_J|`, `‖A_J⁻¹‖_F`, leverages, and the pivot
trajectory. Compare CPQR to exhaustive optimum on small `n`.

The research question is whether `r_CPQR` stays bounded or grows.

## What this skill may claim

- Census numbers are witnesses, not theorems.
- `r_CPQR > 1` on one matrix is a counterexample to the *ideal*
  `C = 1` workshop-scale bound, not to `poly(n,k)`.
- A `poly(n,k)` disproof needs a certified family whose inverse norm
  grows superpolynomially, or a single certified instance that already
  exceeds every reasonable polynomial the project named. Do not blur
  these.

## Implementation targets

- Python generators and JSON census: `structselect/census.py`
- Tests must not assert a universal bound
- Lean formalization only after SPEC §9 certification steps
