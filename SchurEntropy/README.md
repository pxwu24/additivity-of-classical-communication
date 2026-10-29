# Lean source organization

The three completed matrix results are exported by [Results.lean](Results.lean):

- `optimizedConcavity`: minimum attainment and concavity of the optimized deficit.
- `scalar_joint_convexity`: joint convexity of the scalar deficit.
- `block_entropy_inequality`: the Schur-weighted block entropy inequality.

The two completed entropic criteria are exported by [Capacity/Results.lean](Capacity/Results.lean):

- `Capacity.standard_entropic_criterion`: preserving both reduced states implies Holevo additivity.
- `Capacity.output_center_entropic_criterion`: preserving the first output-center expectation and the second reduced state implies Holevo additivity, including singular centers.

[Qubit/Results.lean](Qubit/Results.lean) exports Result 2:

- `Qubit.single_coherent_qubit_output_additivity`: arbitrary finite input dimension, one coherent Kraus operator, and two positive commuting-output effects.
- `Qubit.all_qubit_channels_additivity`: every qubit-to-qubit channel, with an arbitrary finite-dimensional partner.

[Qubit/DecompositionGeneral.lean](Qubit/DecompositionGeneral.lean) proves the full qubit-output decomposition lemma in arbitrary input dimension, with exactly `dim(input) - 1` coherent Kraus slots after zero padding. The all-qubit theorem specializes this construction to input dimension two.

[Definitions.lean](Definitions.lean) defines unnormalized spectral entropy in bits and the exact matrix statements. [Capacity/Definitions.lean](Capacity/Definitions.lean) and [Capacity/CriterionStatements.lean](Capacity/CriterionStatements.lean) define the channel quantities and both criterion hypotheses. [SchurEntropy.lean](../SchurEntropy.lean) collects the results.

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
| `Capacity/Definitions`, `Capacity/StandardCriterion` | Concrete CPTP channels, finite-ensemble Holevo supremum in bits, and the standard criterion |
| `Capacity/CompactConvexHull`, `Capacity/OptimalEnsemble`, `Capacity/OptimalOutputCenter` | Compactness, attainment of the actual Holevo maximum, and construction of an optimal center |
| `Capacity/LogPairing`, `Capacity/OutputCenterMixture`, `Capacity/RegularizedEntropy`, `Capacity/ScalarLogLimit`, `Capacity/Center*`, `Capacity/Gibbs*`, `Capacity/OutputCenterRadius` | Optimality perturbation, singular-center support inclusion, logarithmic limits, and derived Gibbs/radius bounds |
| `Capacity/WeakReduction`, `Capacity/CriterionStatements`, `Capacity/OutputCenterCriterion` | Finite-ensemble reduction, standard-to-weaker implication, and the complete weaker criterion |
| `Qubit/OutputForm`, `Qubit/Representation`, `Qubit/Decomposition*` | Concrete Kraus/effect representations and output-basis selection |
| `Qubit/PSDFactor`, `Qubit/RankFactorization`, `Qubit/RankPadding` | Rank-sized PSD block factors, singular limits, and zero padding to the stated number of Kraus operators |
| `Qubit/Ensemble*` | Balanced pure-state ensembles in arbitrary input dimension and the scalar entropy bound |
| `Qubit/BlockEntropyBridge`, `Qubit/ChannelBound*`, `Qubit/Results` | Specialization of the Schur theorem, exact compatible ensembles, and strong additivity |

See the [verification index](../docs/verification.md) for exact declarations, reproducible build instructions, and axiom checks. The weaker entropic criterion applies to any specified optimal ensemble; it does not require a separate uniqueness theorem for the center. The phase-covariant application remains future formalization work.
