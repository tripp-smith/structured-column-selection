import StructuredColumnSelection.Definitions
import StructuredColumnSelection.PrincipalColumns
import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.SmallInstanceChecks
import StructuredColumnSelection.Theorems

/-!
# StructuredColumnSelection

Root module for the Lean 4 / mathlib4 formalization plan in `SPEC.md`.
Current status executes Milestones A–D and the Milestone E structural
CPQR layer: leverage scores, first-pivot maximality, and the full-rank
card identity `#(cpqrSet A) = k`. No polynomial CPQR bound is claimed.
-/
