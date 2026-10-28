# Lean source organization

The three completed manuscript results are exported by [Results.lean](Results.lean):

- `optimizedConcavity`: minimum attainment and concavity of the optimized deficit.
- `scalar_joint_convexity`: joint convexity of the scalar deficit.
- `block_entropy_inequality`: the Schur-weighted block entropy inequality.

[Definitions.lean](Definitions.lean) defines unnormalized spectral entropy in bits and the exact theorem statements. [SchurEntropy.lean](../SchurEntropy.lean) collects the proof library.

The source is organized into these groups:

| Modules | Purpose |
| --- | --- |
| `Isometry`, `RankOne*`, `EntropyIncrement`, `BlockTraceBound` | Complete rank-one proof, including zero block traces and singular noise |
| `Reduction`, `SpectralDecomposition`, `BlockReduction` | Finite convex decomposition and Jensen argument |
| `SupportingMultiplier`, `BlockBoundary`, `BlockTheorem` | Supporting functional, semidefinite boundary, and assembly of the main theorem |
| `ScalarKernel`, `ScalarHessian`, `ScalarConvexity*` | Spectral entropy calculus, Hessian estimate, and scalar joint convexity |
| `BlockAlgebra`, `MultiBlock*` | Matrix comparison and curvature estimates for arbitrary finite block families |
| `Optimized*` | Attainment, interior minimizers, implicit differentiation, concavity, boundary extension, and conversion to bits |
| `EntropyScaling`, `EntropyContinuity` | General unnormalized entropy identities and continuity |

See the [verification index](../docs/verification.md) for source links, exact declarations, reproducible build instructions, and axiom checks. The channel-capacity applications and entropic criteria remain future formalization work.
