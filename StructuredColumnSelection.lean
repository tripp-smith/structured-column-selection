import StructuredColumnSelection.Definitions
import StructuredColumnSelection.PrincipalColumns
import StructuredColumnSelection.OrthogonalRows
import StructuredColumnSelection.CauchyBinet
import StructuredColumnSelection.VolumeWeights
import StructuredColumnSelection.InverseGramExpectation
import StructuredColumnSelection.InverseNormBounds
import StructuredColumnSelection.ColumnPivotedQR
import StructuredColumnSelection.ResidualEnergy
import StructuredColumnSelection.CPQRVolume
import StructuredColumnSelection.PrefixInverse
import StructuredColumnSelection.TriangularBound
import StructuredColumnSelection.ResidualMono
import StructuredColumnSelection.SigmaMinBounds
import StructuredColumnSelection.RowOrthoConstraints
import StructuredColumnSelection.SmallInstanceChecks
import StructuredColumnSelection.Theorems

/-!
# StructuredColumnSelection

Root module for the Lean 4 / mathlib4 formalization plan in `SPEC.md`.
Current status executes Milestones A–D and the Milestone E structural
CPQR layer, plus residual energy, the `k = 1` volume bound,
contraction / last-residual lemmas, and the inverse-Frobenius /
leave-one-out residual identity. No polynomial CPQR bound for
general `k` is claimed.
-/
