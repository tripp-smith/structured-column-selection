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

## Formal path that still leaves E open

After the §8 census, prefer Lean identities that constrain CPQR
without claiming `poly(n,k)`:

1. Residual energy: if `J` is independent, `∑_j residualSq A J j = k-#J`.
   Then the next unused residual is at least `(k-#J)/(n-#J)`.
2. Volume product: successive pivot residuals multiply to
   `volumeWeight A (cpqrSet A)`, hence
   `volumeWeight ≥ 1 / C(n,k)`. That is exponential in `k` for
   `n ≈ 2k`, so it is **not** outcome 1.
3. The `k = 1` case is a genuine workshop-scale inverse bound
   (`|A_{0j}|⁻¹ ≤ √n`). It does **not** close E for general `k`.

Do not treat “every census sample had `r_CPQR < 1`” as evidence of a
universal `C = 1` theorem.

## Implementation targets

- Python generators and JSON census: `structselect/census.py`
- Tests must not assert a universal bound
- Lean residual-energy / `k = 1` theorems may ship without a
  counterexample
- A Lean counterexample is allowed only after SPEC §9 certification
