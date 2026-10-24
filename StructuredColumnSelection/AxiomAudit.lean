import StructuredColumnSelection.Theorems

/-!
# Public-theorem axiom audit

This module is a verification companion, not a source of theorems.
It `#print axioms` every public name in `Theorems.lean`. Run it with

```
lake env lean --stdin < StructuredColumnSelection/AxiomAudit.lean
```

or via `bash scripts/verify.sh`. Do **not** use `lake env lean --run`.

Public structural theorems may depend only on `propext`,
`Classical.choice`, and `Quot.sound`. `native_decide` witnesses stay in
`SmallInstanceChecks.lean` and are not listed here.
-/

#print axioms StructuredColumnSelection.milestoneA_transpose_correspondence
#print axioms StructuredColumnSelection.milestoneA_selectedSquare_entry
#print axioms StructuredColumnSelection.milestoneA_selectedGram_formula
#print axioms StructuredColumnSelection.milestoneB_volume_normalization
#print axioms StructuredColumnSelection.milestoneB_cauchyBinet
#print axioms StructuredColumnSelection.milestoneC_inverse_gram_expectation
#print axioms StructuredColumnSelection.milestoneC_adjugate_sum
#print axioms StructuredColumnSelection.milestoneD_expected_inv_frob_sq
#print axioms StructuredColumnSelection.milestoneD_markov_inv_frob
#print axioms StructuredColumnSelection.milestoneE_residual_empty
#print axioms StructuredColumnSelection.milestoneE_cpqr_card_le
#print axioms StructuredColumnSelection.milestoneE_leverage_sum
#print axioms StructuredColumnSelection.milestoneE_first_pivot_is_max
#print axioms StructuredColumnSelection.milestoneE_cpqr_card_eq
#print axioms StructuredColumnSelection.milestoneE_first_leverage_ge
#print axioms StructuredColumnSelection.milestoneE_k1_volume_ge
#print axioms StructuredColumnSelection.milestoneE_k2_inv_trace_le
#print axioms StructuredColumnSelection.milestoneE_residual_energy
#print axioms StructuredColumnSelection.milestoneE_next_residual_ge
#print axioms StructuredColumnSelection.milestoneE_cpqr_volume_ge_binomial
#print axioms StructuredColumnSelection.milestoneE_mulVec_energy_le
#print axioms StructuredColumnSelection.milestoneE_col_energy_le
#print axioms StructuredColumnSelection.milestoneE_last_residual_ge
#print axioms StructuredColumnSelection.milestoneE_pivot_gram_inv_trace_le
#print axioms StructuredColumnSelection.milestoneE_residual_antitone
#print axioms StructuredColumnSelection.milestoneE_residual_insert_downdate
#print axioms StructuredColumnSelection.milestoneE_gram_inv_trace_eq_sum_inv_residual
#print axioms StructuredColumnSelection.milestoneE_sigma_min_ge_inv_sqrt_trace
#print axioms StructuredColumnSelection.milestoneE_gsR_mul_transpose
#print axioms StructuredColumnSelection.milestoneE_bidiagonal_U_inv_trace_le
