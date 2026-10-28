import SchurEntropy.BlockTheorem
import SchurEntropy.OptimizedBridge
import SchurEntropy.ScalarConvexity

/-!
# The three manuscript results

The two analytic lemmas and the block entropy inequality use the concrete
spectral von Neumann entropy in bits from `Definitions`. The declarations
below introduce no additional analytic assumptions.
-/

namespace SchurEntropy

/-- The Schur-weighted block entropy inequality for arbitrary finite positive
block dimensions and positive semidefinite input matrices. -/
theorem block_entropy_inequality : BlockEntropyStatement :=
  blockEntropy_of_two_lemmas optimizedConcavity scalar_joint_convexity

-- These explicit type checks prevent accidental strengthening of hypotheses
-- in the exported proofs of the manuscript's three statements.
example : OptimizedConcavityStatement := optimizedConcavity
example : ScalarConvexityStatement := scalar_joint_convexity
example : BlockEntropyStatement := block_entropy_inequality

end SchurEntropy
