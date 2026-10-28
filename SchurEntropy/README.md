# Planned Lean modules

This directory is reserved for the formal proofs accompanying the manuscript. The paths below describe the proposed organization; the `.lean` files have not yet been added.

| Planned path | Scope |
| --- | --- |
| `Entropy/Definitions.lean` | Entropy of positive operators, block pinching, Schur products, and entropy deficit |
| `Entropy/OptimizedConcavity.lean` | Attainment of the minimum and concavity after optimization |
| `Entropy/ScalarConvexity.lean` | Joint convexity in the scalar trace parameters |
| `Entropy/BlockInequality.lean` | Schur-weighted block entropy inequality |
| `Capacity/Definitions.lean` | Finite ensembles, Holevo information, and optimal output centers |
| `Capacity/StandardCriterion.lean` | Entropic criterion preserving both reduced input states |
| `Capacity/OutputCenterCriterion.lean` | Weaker criterion preserving one output-center expectation |
| `Channels/PhaseCovariant.lean` | Phase-covariant channel structure and strong additivity |
| `Channels/QubitOutput.lean` | Qubit-output decomposition, qubit-to-qubit coverage, and strong additivity |

The channel applications need both the entropy inequality and their channel-structure arguments. For qubit-to-qubit channels, the decomposition assertion must be included in the formalization as well as the additivity implication.

When the proof sources are incorporated, a root `SchurEntropy.lean` import file will collect the checked modules, and the Lean toolchain and dependencies will be pinned to the versions used by those sources.

See the [mathematical overview](../README.md) and [verification index](../docs/verification.md).
