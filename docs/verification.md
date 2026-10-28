# Verification status

The two analytic lemmas and the Schur-weighted block entropy inequality are proved in Lean 4. Their exported theorems have no additional analytic hypotheses. The definitions use actual complex matrices and unnormalized spectral entropy in bits, with `0 log 0 = 0`.

## Completed manuscript results

| Manuscript result | Lean declaration | Source |
| --- | --- | --- |
| Minimum attainment and optimized concavity | `SchurEntropy.optimizedConcavity : OptimizedConcavityStatement` | [OptimizedBridge.lean](../SchurEntropy/OptimizedBridge.lean) |
| Scalar joint convexity | `SchurEntropy.scalar_joint_convexity : ScalarConvexityStatement` | [ScalarConvexity.lean](../SchurEntropy/ScalarConvexity.lean) |
| Schur-weighted block entropy inequality | `SchurEntropy.block_entropy_inequality : BlockEntropyStatement` | [Results.lean](../SchurEntropy/Results.lean) |

[Definitions.lean](../SchurEntropy/Definitions.lean) specifies the exact three propositions. [Results.lean](../SchurEntropy/Results.lean) and [Audit.lean](../Audit.lean) explicitly check that the exported proofs have those types.

The optimized lemma proves attainment of the literal `sInf`-defined value over all positive semidefinite block-diagonal noise matrices, as well as concavity on the whole PSD cone. The scalar lemma includes singular coefficient matrices and zero trace parameters. The block theorem covers arbitrary positive finite block dimensions and PSD `C`, `H`, and block-diagonal `W`; no trace normalization or unit-diagonal assumption on `C` is imposed.

The channel-capacity applications and the two entropic criteria in the README have not yet been formalized in this repository. Their mathematical statements remain part of the manuscript overview.

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
- Auxiliary matrix-calculus library `qubitStrongAdditivity`, commit `90e61c463deb42067c109c46f048c6374dfc5945`.

The root Mathlib pin overrides the auxiliary library's declared version. The imported dependency chain was compiled with this configuration, without modifying either dependency's source.

With Lean's `elan` version manager installed, run from the repository root:

```sh
lake exe cache get
./scripts/check.sh
```

The [check script](../scripts/check.sh) runs the project build and [Audit.lean](../Audit.lean). The audit traverses every imported declaration in the `SchurEntropy` namespace and rejects any transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects `sorryAx`. It also prints the transitive axioms and checks the exact types of all three completed manuscript results.

Source provenance and the licenses of adapted excerpts are recorded in [third_party/NOTICE](../third_party/NOTICE).
