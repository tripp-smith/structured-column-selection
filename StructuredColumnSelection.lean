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
CPQR layer, plus residual energy, residual monotonicity, the `k = 1`
volume bound, the `k = 2` inverse-trace bound (bidiagonal `U` is
automatic on `Fin 2`), contraction / last-residual lemmas, the
inverse-Frobenius / leave-one-out residual identity, and `R Rᵀ = I`
for the implicit CPQR factor. A polynomial inverse-trace bound for
general `k` is proved only under a bidiagonal hypothesis on `U`, not
for every orthogonal-row matrix. No joint `poly(n,k)` CPQR bound for
general `k` is claimed. Milestone E remains open.
-/
