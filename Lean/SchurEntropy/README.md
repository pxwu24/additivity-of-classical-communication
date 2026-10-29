# Lean source organization

This directory contains the formal proofs accompanying **“Classical communication over quantum channels: does entanglement help in nature?”** The project is presented as **Additivity of classical communication**; its Lean namespace remains `SchurEntropy`, reflecting the central block entropy inequality.

The entry points below follow the manuscript’s order. The capacity coding theorems in Section 1 are background, not separate results of this formalization.

## Section 2: entropic criteria

The two completed entropic criteria are exported by [Capacity/Results.lean](Capacity/Results.lean):

- `Capacity.standard_entropic_criterion`: preserving both reduced states implies Holevo additivity.
- `Capacity.output_center_entropic_criterion`: preserving the first output-center expectation and the second reduced state implies Holevo additivity, including singular centers.

## Section 3: the block entropy inequality

The three completed matrix results are exported by [Results.lean](Results.lean):

- `optimizedConcavity`: minimum attainment and concavity of the optimized deficit.
- `scalar_joint_convexity`: joint convexity of the scalar deficit.
- `block_entropy_inequality`: the Schur-weighted block entropy inequality.

## Section 4: phase-covariant channels

[PhaseCovariant/Results.lean](PhaseCovariant/Results.lean) exports the phase-covariant application:

- `PhaseCovariant.phase_covariant_additivity`: covariance under all diagonal unitaries in one fixed basis implies strong additivity against every finite-dimensional partner.
- `PhaseCovariant.phase_covariant_angles_additivity`: the same conclusion with the manuscript's real-phase parametrization.
- `PhaseCovariant.phase_covariant_states_additivity`: covariance need only be checked on density matrices.
- `PhaseCovariant.phase_covariant_in_basis_additivity`: a specified unitary chooses any fixed orthonormal basis.
- `PhaseCovariant.normal_form_additivity`: the corresponding theorem for a specified Schur-plus-classical normal form.

[PhaseCovariant/NormalForm.lean](PhaseCovariant/NormalForm.lean) proves both directions of the normal-form characterization from actual covariance and CPTP. Finite sign averaging constructs an actual optimal ensemble with diagonal output center, and the local block-entropy bridge supplies the weaker criterion's entropy estimate.

## Section 5: qubit-output channels

[Qubit/Results.lean](Qubit/Results.lean) exports the single-coherent-Kraus application and the all-qubit recovery:

- `Qubit.single_coherent_qubit_output_additivity`: arbitrary finite input dimension, one coherent Kraus operator, and two positive commuting-output effects.
- `Qubit.all_qubit_channels_additivity`: every qubit-to-qubit channel, with an arbitrary finite-dimensional partner.

[Qubit/DecompositionGeneral.lean](Qubit/DecompositionGeneral.lean) proves the full qubit-output decomposition lemma in arbitrary input dimension, with exactly `dim(input) - 1` coherent Kraus slots after zero padding. The all-qubit theorem specializes this construction to input dimension two.

The all-qubit result recovers Kenta Kitamura’s theorem; see [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity). The project uses the pinned upstream matrix/channel library and adapts proof components, as recorded in [third_party/NOTICE](../third_party/NOTICE). Its channel entropy bounds are derived locally from the Schur-weighted block theorem.

The general decomposition lemma does not establish additivity with several coherent Kraus operators. Strong additivity for every qubit-output channel, and the manuscript’s conjecture about a dimension threshold for classical-capacity additivity, remain open directions rather than exported Lean theorems.

## Definitions and module map

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
| `PhaseCovariant/Definitions`, `PhaseCovariant/CharacterSupport`, `PhaseCovariant/NormalForm`, `PhaseCovariant/CovarianceOnStates` | Genuine fixed-basis covariance, matrix-unit characters, the proved normal form, and equivalence of state-only covariance |
| `PhaseCovariant/SignAveraging`, `PhaseCovariant/OptimalCenter` | Finite symmetrization of an attaining ensemble and a diagonal optimal output center |
| `PhaseCovariant/ComparisonState`, `PhaseCovariant/LogCompatibility` | Positive-amplitude comparison input and the weaker logarithmic compatibility |
| `PhaseCovariant/BlockEntropyBridge`, `PhaseCovariant/NoiseEntropy`, `PhaseCovariant/EntropyBound*` | General block-entropy specialization, noise concavity, and the exact pure-input bound |
| `PhaseCovariant/UnitaryInvariance`, `PhaseCovariant/Results` | Basis changes, weaker-criterion assembly, and strong additivity |
| `Qubit/OutputForm`, `Qubit/Representation`, `Qubit/Decomposition*` | Concrete Kraus/effect representations and output-basis selection |
| `Qubit/PSDFactor`, `Qubit/RankFactorization`, `Qubit/RankPadding` | Rank-sized PSD block factors, singular limits, and zero padding to the stated number of Kraus operators |
| `Qubit/Ensemble*` | Balanced pure-state ensembles in arbitrary input dimension and the scalar entropy bound |
| `Qubit/BlockEntropyBridge`, `Qubit/ChannelBound*`, `Qubit/Results` | Specialization of the Schur theorem, exact compatible ensembles, and strong additivity |

See the [verification index](../verification.md) for exact declarations, reproducible build instructions, and axiom checks. The weaker entropic criterion applies to any specified optimal ensemble; the phase-covariant proof uses its symmetrized optimum and does not require a separate uniqueness theorem for the center.
