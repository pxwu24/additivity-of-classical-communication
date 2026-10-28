# Verification status

This initial repository contains documentation only. No Lean proof sources have been supplied or incorporated, and no Lean build has been run. The mathematical statements in the README are the statements supplied for the forthcoming manuscript.

## Result index

| Result | Planned module | Source and declaration | Status |
| --- | --- | --- | --- |
| Phase-covariant strong additivity | `SchurEntropy.Channels.PhaseCovariant` | Pending | Pending source |
| Qubit-output strong additivity and qubit-to-qubit coverage | `SchurEntropy.Channels.QubitOutput` | Pending | Pending source |
| Standard entropic criterion | `SchurEntropy.Capacity.StandardCriterion` | Pending | Pending source |
| Weaker output-center criterion | `SchurEntropy.Capacity.OutputCenterCriterion` | Pending | Pending source |
| Schur-weighted block entropy inequality | `SchurEntropy.Entropy.BlockInequality` | Pending | Pending source |
| Optimized concavity and attainment | `SchurEntropy.Entropy.OptimizedConcavity` | Pending | Pending source |
| Scalar joint convexity | `SchurEntropy.Entropy.ScalarConvexity` | Pending | Pending source |

## Reproducible verification

As proof files are added, each entry will record its exact source path, theorem declaration, assumptions, and the commit at which it was checked. A successful project build will be distinguished from verification of an individual manuscript theorem.

The first source import will include the matching `lean-toolchain`, Lake configuration, and dependency lockfile. Build instructions and continuous integration will then use those pinned versions.

A completed result must have a corresponding Lean statement matching the manuscript, compile with the pinned environment, and contain no unfinished `sorry`/`admit` proof. Its transitive axioms will be inspected with `#print axioms`; any mathematical assumptions beyond Lean's standard foundations will be recorded explicitly. A conditional proof will be identified as conditional.

## Conventions to match

- Entropy uses base-two logarithms and is defined on unnormalized positive semidefinite matrices, with `0 log 0 = 0`.
- The block and scalar deficits use their respective pinching maps.
- The output-center logarithm is interpreted on its support.
- Phase covariance is with respect to all diagonal unitaries in a fixed basis.
- Strong additivity quantifies over arbitrary finite-dimensional partner channels.

[Return to the overview](../README.md).
