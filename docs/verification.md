# Verification status

This index records the formalized results accompanying **“Classical communication over quantum channels: does entanglement help in nature?”** The central Schur-weighted block entropy inequality, its two analytic lemmas, both entropic criteria, the phase-covariant application, and the qubit-output application (including the all-qubit recovery) are proved in Lean 4. Their exported theorems have exactly the stated mathematical hypotheses. The definitions use actual complex matrices and spectral entropy in bits, with `0 log 0 = 0`; the channel results use concrete completely positive trace-preserving maps and finite ensembles of density matrices.

## Manuscript and formalization scope

| Manuscript section | Scope in this repository |
| --- | --- |
| 1. Introduction | The capacity question and coding theorems provide background; the coding theorems are not separately formalized |
| 2. Entropic criteria | Both sufficient criteria, finite-ensemble attainment, and support and center bounds |
| 3. Block entropy inequality | The central inequality, optimized concavity with attainment, and scalar joint convexity |
| 4. Phase-covariant channels | Fixed-basis normal form and strong additivity with every finite-dimensional partner |
| 5. Qubit-output channels | General decomposition, the single-coherent-Kraus theorem, and recovery of all-qubit strong additivity |
| Discussion | Multiple-coherent-Kraus qubit-output additivity and the dimension-threshold conjecture remain open directions |

## Completed results

| Manuscript result | Lean declaration | Source |
| --- | --- | --- |
| Minimum attainment and optimized concavity | `SchurEntropy.optimizedConcavity : OptimizedConcavityStatement` | [OptimizedBridge.lean](../SchurEntropy/OptimizedBridge.lean) |
| Scalar joint convexity | `SchurEntropy.scalar_joint_convexity : ScalarConvexityStatement` | [ScalarConvexity.lean](../SchurEntropy/ScalarConvexity.lean) |
| Schur-weighted block entropy inequality | `SchurEntropy.block_entropy_inequality : BlockEntropyStatement` | [Results.lean](../SchurEntropy/Results.lean) |
| Standard entropic criterion | `SchurEntropy.Capacity.standard_entropic_criterion` | [StandardCriterion.lean](../SchurEntropy/Capacity/StandardCriterion.lean) |
| Weaker output-center criterion | `SchurEntropy.Capacity.output_center_entropic_criterion` | [OutputCenterCriterion.lean](../SchurEntropy/Capacity/OutputCenterCriterion.lean) |
| All fixed-basis phase-covariant channels | `SchurEntropy.PhaseCovariant.phase_covariant_additivity` | [PhaseCovariant/Results.lean](../SchurEntropy/PhaseCovariant/Results.lean) |
| Fixed-basis phase-covariant normal form | `SchurEntropy.PhaseCovariant.phaseCovariant_iff_normalForm` | [NormalForm.lean](../SchurEntropy/PhaseCovariant/NormalForm.lean) |
| Single-coherent-Kraus qubit-output channels | `SchurEntropy.Qubit.single_coherent_qubit_output_additivity` | [Qubit/Results.lean](../SchurEntropy/Qubit/Results.lean) |
| All qubit-to-qubit channels | `SchurEntropy.Qubit.all_qubit_channels_additivity` | [Qubit/Results.lean](../SchurEntropy/Qubit/Results.lean) |
| General qubit-output decomposition | `SchurEntropy.Qubit.exists_qubit_output_decomposition_general` | [DecompositionGeneral.lean](../SchurEntropy/Qubit/DecompositionGeneral.lean) |

[Definitions.lean](../SchurEntropy/Definitions.lean) specifies the three matrix propositions. [Capacity/Definitions.lean](../SchurEntropy/Capacity/Definitions.lean) and [Capacity/CriterionStatements.lean](../SchurEntropy/Capacity/CriterionStatements.lean) specify the two entropic hypotheses. [Audit.lean](../Audit.lean) checks the exported matrix types and both channel conclusions with their full ensemble hypotheses exposed.

The optimized lemma proves attainment of the literal `sInf`-defined value over all positive semidefinite block-diagonal noise matrices, as well as concavity on the whole PSD cone. The scalar lemma includes singular coefficient matrices and zero trace parameters. The block theorem covers arbitrary positive finite block dimensions and PSD `C`, `H`, and block-diagonal `W`; no trace normalization or unit-diagonal assumption on `C` is imposed.

Both criteria conclude `holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω` for arbitrary finite-dimensional CPTP maps with nonempty input spaces. The standard hypothesis preserves both reduced input states. The weaker hypothesis preserves only the first output's logarithmic expectation at an optimal center, together with the second reduced input state. Both require the manuscript's entropy bound for every bipartite pure input.

The classical-capacity coding and regularization theorems and uniqueness of the optimal output center are not separately formalized here.

## Entropic-criterion foundations

`holevoInformation` is proved equal to the supremum of the actual finite-ensemble entropy expressions in bits. [OptimalEnsemble.lean](../SchurEntropy/Capacity/OptimalEnsemble.lean) proves that this supremum is attained: it takes a maximum over the compact convex hull of the graph of output state and output entropy, then realizes that point by a finite ensemble. [OptimalOutputCenter.lean](../SchurEntropy/Capacity/OptimalOutputCenter.lean) constructs a center from this proved existence.

The weaker criterion also has the reusable form `output_center_criterion_of_optimal_ensemble`, for the average output of any specified optimal ensemble. Optimality means equality with the original Holevo supremum; no radius or support property is built into that definition. The proof therefore does not require uniqueness of the center.

For singular centers, [OutputCenterRadius.lean](../SchurEntropy/Capacity/OutputCenterRadius.lean) derives support inclusion, the Gibbs bound, and the relative-entropy radius bound from actual ensemble optimality. The proof perturbs an optimal ensemble by an arbitrary input state, obtains a lower bound on the regularized logarithmic pairing, and proves its finite limit spectrally. In particular, `optimal_center_support` proves that every channel output is supported in the optimal center. The logarithm's zero extension on the kernel consequently agrees with the intended support interpretation.

[WeakReduction.lean](../SchurEntropy/Capacity/WeakReduction.lean) extends the pure-input hypothesis to mixed inputs and finite ensembles. [OutputCenterCriterion.lean](../SchurEntropy/Capacity/OutputCenterCriterion.lean) supplies the proved center bounds and converts the resulting Holevo equality to bits. The final theorem has no full-rank, support, Gibbs, radius, or optimum-existence assumption. The standard criterion uses the generic finite-ensemble proof in the pinned `QubitAdditivity.UpperBound` dependency; its equivalence to the bit-valued hypothesis is proved locally.

The implication from the standard hypothesis to the weaker hypothesis is proved by `standard_implies_outputCenter` in [CriterionStatements.lean](../SchurEntropy/Capacity/CriterionStatements.lean).

## Block-entropy supporting results

| Result | Source | Declaration |
| --- | --- | --- |
| Rank-one inequality, including zero block traces and singular noise | [RankOneInequality.lean](../SchurEntropy/RankOneInequality.lean) | `rankOne_block_entropy` |
| Entropy increment is antitone in PSD noise | [EntropyIncrement.lean](../SchurEntropy/EntropyIncrement.lean) | `entropy_increment_antitone` |
| Isometry invariance and cancellation of unused block dimensions | [RankOneEntropy.lean](../SchurEntropy/RankOneEntropy.lean) | `entropy_blockColumns_increment` |
| Finite convex rank-one decomposition | [SpectralDecomposition.lean](../SchurEntropy/SpectralDecomposition.lean) | `exists_uniform_rankOne_decomposition` |
| Main theorem from the two analytic lemmas | [BlockTheorem.lean](../SchurEntropy/BlockTheorem.lean) | `blockEntropy_of_two_lemmas` |
| Negative supporting multiplier | [SupportingMultiplier.lean](../SchurEntropy/SupportingMultiplier.lean) | `SupportingMultiplier.exists_negative_support` |
| Extension from positive definite to semidefinite inputs | [BlockBoundary.lean](../SchurEntropy/BlockBoundary.lean) | `blockEntropy_of_posDef` |
| Matrix Hessian estimate for scalar convexity | [ScalarHessian.lean](../SchurEntropy/ScalarHessian.lean) | `ScalarHessian.hessian_nonneg` |
| Stationary matrix comparison for arbitrary finite blocks | [MultiBlockComparison.lean](../SchurEntropy/MultiBlockComparison.lean) | `MultiBlock.km_of_stationarity` |
| Optimized value Hessian bound | [OptimizedHessian.lean](../SchurEntropy/OptimizedHessian.lean) | `Optimized.valueHessianRow_self_nonpos` |

The main theorem follows the manuscript's rank-one reduction, optimization, and finite convex-combination argument. The logarithms in the analytic matrix calculus are natural logarithms; the bridge modules prove the conversion to bits, including the multiplier rescaling by `log 2`.

## Phase-covariant application

[PhaseCovariant/Definitions.lean](../SchurEntropy/PhaseCovariant/Definitions.lean) defines covariance independently of any normal form, as commutation with conjugation by every diagonal unitary in one fixed basis. It proves equivalence with the manuscript's real-angle parametrization. [NormalForm.lean](../SchurEntropy/PhaseCovariant/NormalForm.lean) proves the characterization in both directions: matrix-unit characters force the entrywise action, a principal Choi submatrix supplies the positive Schur coefficient matrix, and trace preservation gives the column-stochastic transition coefficients.

[CovarianceOnStates.lean](../SchurEntropy/PhaseCovariant/CovarianceOnStates.lean) proves that testing covariance only on density matrices is equivalent to the full linear-map identity. `phase_covariant_states_additivity` accepts precisely that state-only, real-angle hypothesis. `phase_covariant_in_basis_additivity` allows any specified fixed orthonormal basis, represented by a unitary. The dimension assumptions are only finite, nonempty input spaces; one-dimensional channels are included.

[OptimalCenter.lean](../SchurEntropy/PhaseCovariant/OptimalCenter.lean) starts with an actually attaining finite ensemble and averages over all diagonal sign unitaries. Its average output is diagonal, individual output entropies are unchanged, and entropy concavity shows that the new ensemble remains optimal. This constructs the center needed for the weaker criterion without assuming uniqueness.

[ComparisonState.lean](../SchurEntropy/PhaseCovariant/ComparisonState.lean) constructs the positive-amplitude pure input with the same diagonal as the original first marginal. [LogCompatibility.lean](../SchurEntropy/PhaseCovariant/LogCompatibility.lean) proves that a diagonal output-center logarithm sees only this diagonal, including when the center is singular. The support justification is inherited from the proved optimal-center criterion.

[BlockEntropyBridge.lean](../SchurEntropy/PhaseCovariant/BlockEntropyBridge.lean) derives the arbitrary-block entropy estimate from this repository's Schur-weighted theorem. [EntropyBound.lean](../SchurEntropy/PhaseCovariant/EntropyBound.lean) applies it to the actual joint channel output. Unnormalized branch vectors, scalar entropy scaling, concavity for each noise mixture, and column stochasticity yield the comparison-input entropy plus the average partner-output entropy. Zero branches retain zero weight and do not require division by zero.

[Results.lean](../SchurEntropy/PhaseCovariant/Results.lean) assembles explicit finite ensembles and invokes `output_center_criterion_of_optimal_ensemble`. The final covariance theorem has no normal-form, entropy-bound, center, or optimizer hypothesis. [UnitaryInvariance.lean](../SchurEntropy/PhaseCovariant/UnitaryInvariance.lean) proves invariance under a fixed change of input and output coordinates, also after tensoring with an arbitrary partner. The [proof review](phase-covariant-proof-review.md) gives the corrected mathematical argument and identifies the two mistaken identities in the submitted draft.

## Qubit-output application and all-qubit recovery

[Qubit/Representation.lean](../SchurEntropy/Qubit/Representation.lean) gives the literal single coherent Kraus operator and two positive effects. The final theorem accepts an output unitary, arbitrary coherent vectors, positive semidefinite effects, the stated completeness identity, and equality of the channel formula on all complex input matrices. No scalar entropy bound, block inequality, or entropic criterion is assumed in its final statement.

[Qubit/EnsembleBound.lean](../SchurEntropy/Qubit/EnsembleBound.lean) constructs a finite ensemble preserving the first reduced state and balancing the two coherent probabilities. The formal construction uses a finite spectral sign frame in place of the manuscript's Fourier basis. Both give the same zero-expectation property. For each positive-weight atom, the two-by-two output entropy agrees with that of its phase-aligned scalar matrix; the formal proof establishes this using equality of trace and determinant. Zero atoms contribute zero without division by zero.

[Qubit/BlockEntropyBridge.lean](../SchurEntropy/Qubit/BlockEntropyBridge.lean) derives the required four-block entropy inequality directly from `SchurEntropy.block_entropy_inequality`, using the all-ones two-by-two coefficient matrix. [Qubit/ChannelBound.lean](../SchurEntropy/Qubit/ChannelBound.lean) combines it with the scalar bound and a compatible partner ensemble to prove the standard entropic criterion. The partner ensemble resolves the two noise effects into pure Kraus branches; entropy concavity justifies this refinement. [Qubit/Results.lean](../SchurEntropy/Qubit/Results.lean) applies the already-verified standard criterion and output-unitary invariance.

[Qubit/DecompositionGeneral.lean](../SchurEntropy/Qubit/DecompositionGeneral.lean) proves the full decomposition lemma for every channel from a nonempty finite input space to a qubit. A holomorphic determinant polynomial provides a suitable output basis. A rank factorization and positive block-matrix argument produce positive residual effects; zero padding gives exactly `dim(input) - 1` coherent Kraus slots. The statement includes the completeness identity and equality on every complex input matrix, with no invertibility assumption. The formal positive-factor construction uses Schur complements and a compactness limit rather than an explicit pseudoinverse/SVD.

`all_qubit_channels_additivity` specializes this general decomposition to input dimension two and recovers the theorem established by Kenta Kitamura; see [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity). It has only the actual channel arguments and finite, nonempty input spaces. The proof does not import a completed upstream channel-additivity theorem: its entropy estimate comes from this repository's Schur theorem. The pinned Kitamura dependency supplies matrix/channel infrastructure and the proof components generalized here; adaptations are recorded in [third_party/NOTICE](../third_party/NOTICE).

The [proof check](qubit-proof-review.md) supplies the missing details in the manuscript's determinant argument, positivity of the residual effects, support restriction, phase alignment, and zero-weight conventions.

## Discussion: statements not proved here

The decomposition for a channel with input dimension `d` gives at most `d - 1` coherent Kraus operators. The additivity argument handles one such operator, so the general decomposition alone does not prove strong additivity for every qubit-output channel. Extending the entropy estimate to several coherent Kraus operators is an open direction in the manuscript.

The proposed dimension threshold for equality between classical capacity and single-use Holevo information is a conjecture, not an exported Lean declaration. That equality concerns repeated uses of one channel and is weaker than the strong-additivity statements proved here. The discussion does not assert a proved lower bound on the dimension of every possible counterexample.

## Reproduce the verification

The project pins:

- Lean `v4.34.0`.
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Kitamura’s matrix-calculus and channel-entropy library `qubitStrongAdditivity`, commit `90e61c463deb42067c109c46f048c6374dfc5945`: [Github Repository](https://github.com/KitaKen1/qubit-strong-additivity/tree/90e61c463deb42067c109c46f048c6374dfc5945).

The root Mathlib pin overrides the auxiliary library's declared version. The imported dependency chain was compiled with this configuration, without modifying either dependency's source.

With Lean's `elan` version manager installed, run from the repository root:

```sh
lake exe cache get
./scripts/check.sh
```

The [check script](../scripts/check.sh) runs the project build and [Audit.lean](../Audit.lean). The audit traverses every imported declaration in the `SchurEntropy` namespace and rejects any transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects `sorryAx`, including through imported proofs. It also prints the transitive axioms and checks the exact types of the matrix results, both criteria, the weaker criterion for any specified optimal ensemble, the phase-covariant theorem with covariance exposed, the normal-form equivalence, the general decomposition lemma, and both qubit-output conclusions with the positive-effect representation exposed.

Source provenance and the licenses of adapted excerpts are recorded in [third_party/NOTICE](../third_party/NOTICE).

The recorded verification run including the phase-covariant application passed the full build and audited **1,292** imported `SchurEntropy` declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur in their transitive axiom dependencies.
