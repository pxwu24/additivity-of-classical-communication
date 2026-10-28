# Verification status

The two analytic lemmas, the Schur-weighted block entropy inequality, and both entropic criteria for Holevo additivity are proved in Lean 4. Their exported theorems have no additional analytic hypotheses beyond the stated criteria. The definitions use actual complex matrices and spectral entropy in bits, with `0 log 0 = 0`; the channel results use concrete completely positive trace-preserving maps and finite ensembles of density matrices.

## Completed manuscript results

| Manuscript result | Lean declaration | Source |
| --- | --- | --- |
| Minimum attainment and optimized concavity | `SchurEntropy.optimizedConcavity : OptimizedConcavityStatement` | [OptimizedBridge.lean](../SchurEntropy/OptimizedBridge.lean) |
| Scalar joint convexity | `SchurEntropy.scalar_joint_convexity : ScalarConvexityStatement` | [ScalarConvexity.lean](../SchurEntropy/ScalarConvexity.lean) |
| Schur-weighted block entropy inequality | `SchurEntropy.block_entropy_inequality : BlockEntropyStatement` | [Results.lean](../SchurEntropy/Results.lean) |
| Standard entropic criterion | `SchurEntropy.Capacity.standard_entropic_criterion` | [StandardCriterion.lean](../SchurEntropy/Capacity/StandardCriterion.lean) |
| Weaker output-center criterion | `SchurEntropy.Capacity.output_center_entropic_criterion` | [OutputCenterCriterion.lean](../SchurEntropy/Capacity/OutputCenterCriterion.lean) |

[Definitions.lean](../SchurEntropy/Definitions.lean) specifies the three matrix propositions. [Capacity/Definitions.lean](../SchurEntropy/Capacity/Definitions.lean) and [Capacity/CriterionStatements.lean](../SchurEntropy/Capacity/CriterionStatements.lean) specify the two entropic hypotheses. [Audit.lean](../Audit.lean) checks the exported matrix types and both channel conclusions with their full ensemble hypotheses exposed.

The optimized lemma proves attainment of the literal `sInf`-defined value over all positive semidefinite block-diagonal noise matrices, as well as concavity on the whole PSD cone. The scalar lemma includes singular coefficient matrices and zero trace parameters. The block theorem covers arbitrary positive finite block dimensions and PSD `C`, `H`, and block-diagonal `W`; no trace normalization or unit-diagonal assumption on `C` is imposed.

Both criteria conclude `holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω` for arbitrary finite-dimensional CPTP maps with nonempty input spaces. The standard hypothesis preserves both reduced input states. The weaker hypothesis preserves only the first output's logarithmic expectation at an optimal center, together with the second reduced input state. Both require the manuscript's entropy bound for every bipartite pure input.

The phase-covariant and qubit-output applications, the classical-capacity coding and regularization theorems, and uniqueness of the optimal output center are not separately formalized here.

## Entropic-criterion foundations

`holevoInformation` is proved equal to the supremum of the actual finite-ensemble entropy expressions in bits. [OptimalEnsemble.lean](../SchurEntropy/Capacity/OptimalEnsemble.lean) proves that this supremum is attained: it takes a maximum over the compact convex hull of the graph of output state and output entropy, then realizes that point by a finite ensemble. [OptimalOutputCenter.lean](../SchurEntropy/Capacity/OptimalOutputCenter.lean) constructs a center from this proved existence.

The weaker criterion also has the reusable form `output_center_criterion_of_optimal_ensemble`, for the average output of any specified optimal ensemble. Optimality means equality with the original Holevo supremum; no radius or support property is built into that definition. The proof therefore does not require uniqueness of the center.

For singular centers, [OutputCenterRadius.lean](../SchurEntropy/Capacity/OutputCenterRadius.lean) derives support inclusion, the Gibbs bound, and the relative-entropy radius bound from actual ensemble optimality. The proof perturbs an optimal ensemble by an arbitrary input state, obtains a lower bound on the regularized logarithmic pairing, and proves its finite limit spectrally. In particular, `optimal_center_support` proves that every channel output is supported in the optimal center. The logarithm's zero extension on the kernel consequently agrees with the intended support interpretation.

[WeakReduction.lean](../SchurEntropy/Capacity/WeakReduction.lean) extends the pure-input hypothesis to mixed inputs and finite ensembles. [OutputCenterCriterion.lean](../SchurEntropy/Capacity/OutputCenterCriterion.lean) supplies the proved center bounds and converts the resulting Holevo equality to bits. The final theorem has no full-rank, support, Gibbs, radius, or optimum-existence assumption. The standard criterion uses the generic finite-ensemble proof in the pinned `QubitAdditivity.UpperBound` dependency; its equivalence to the bit-valued hypothesis is proved locally.

The implication from the standard hypothesis to the weaker hypothesis is proved by `standard_implies_outputCenter` in [CriterionStatements.lean](../SchurEntropy/Capacity/CriterionStatements.lean).

## Supporting results

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

## Reproduce the verification

The project pins:

- Lean `v4.34.0`.
- Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
- Auxiliary matrix-calculus and channel-entropy library `qubitStrongAdditivity`, commit `90e61c463deb42067c109c46f048c6374dfc5945`.

The root Mathlib pin overrides the auxiliary library's declared version. The imported dependency chain was compiled with this configuration, without modifying either dependency's source.

With Lean's `elan` version manager installed, run from the repository root:

```sh
lake exe cache get
./scripts/check.sh
```

The [check script](../scripts/check.sh) runs the project build and [Audit.lean](../Audit.lean). The audit traverses every imported declaration in the `SchurEntropy` namespace and rejects any transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects `sorryAx`, including through imported proofs. It also prints the transitive axioms and checks the exact types of all five completed manuscript results, as well as the weaker criterion for any specified optimal ensemble.

Source provenance and the licenses of adapted excerpts are recorded in [third_party/NOTICE](../third_party/NOTICE).
