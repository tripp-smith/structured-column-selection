import StructuredColumnSelection.Definitions
import StructuredColumnSelection.PrincipalColumns
import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.CPQRVolume
import StructuredColumnSelection.SmallInstanceChecks
import StructuredColumnSelection.Theorems

/-!
# StructuredColumnSelection

Root module for the Lean 4 / mathlib4 formalization plan in `SPEC.md`.
Current status executes Milestones A–D and the Milestone E structural
CPQR layer, plus residual energy and the `k = 1` volume bound. No
polynomial CPQR bound for general `k` is claimed.
-/
