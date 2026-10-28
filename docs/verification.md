# Verification status

This is an active formalization in Lean 4. The checked source uses actual complex matrices and the unnormalized spectral entropy in bits, with `0 log 0 = 0`. The complete rank-one block entropy inequality is proved. The full arbitrary-rank theorem and the two analytic lemmas are still being assembled; a successful intermediate build does not certify those three statements.

## Checked results

| Result | Source | Declaration |
| --- | --- | --- |
| Rank-one block entropy inequality, including singular noise and zero block traces | [RankOneInequality.lean](../SchurEntropy/RankOneInequality.lean) | `SchurEntropy.rankOne_block_entropy` |
| Entropy increment is antitone in positive semidefinite noise | [EntropyIncrement.lean](../SchurEntropy/EntropyIncrement.lean) | `SchurEntropy.entropy_increment_antitone` |
| Isometry invariance and cancellation of unused block dimensions | [RankOneEntropy.lean](../SchurEntropy/RankOneEntropy.lean) | `SchurEntropy.entropy_blockColumns_increment` |
| Finite convex decomposition into rank-one matrices | [SpectralDecomposition.lean](../SchurEntropy/SpectralDecomposition.lean) | `SchurEntropy.exists_uniform_rankOne_decomposition` |
| Full block theorem conditional only on the two analytic lemmas | [BlockTheorem.lean](../SchurEntropy/BlockTheorem.lean) | `SchurEntropy.blockEntropy_of_two_lemmas` |
| Conditional finite-sum reduction for the general theorem | [BlockReduction.lean](../SchurEntropy/BlockReduction.lean) | `SchurEntropy.blockEntropy_of_analytic_inputs` |
| Full matrix Hessian inequality used for scalar convexity | [ScalarHessian.lean](../SchurEntropy/ScalarHessian.lean) | `SchurEntropy.ScalarHessian.hessian_nonneg` |
| Logarithmic-mean quadratic kernel used for scalar convexity | [ScalarKernel.lean](../SchurEntropy/ScalarKernel.lean) | `SchurEntropy.ScalarKernel.logarithmic_kernel_complex_nonneg` |
| Stationary matrix comparison for arbitrary finite blocks | [MultiBlockComparison.lean](../SchurEntropy/MultiBlockComparison.lean) | `SchurEntropy.MultiBlock.km_of_stationarity` |
| Eliminated matrix curvature under logarithmic stationarity | [MultiBlockHessian.lean](../SchurEntropy/MultiBlockHessian.lean) | `SchurEntropy.MultiBlock.eliminated_expression_nonpos` |

The conditional reduction exposes its remaining analytic hypotheses in its theorem type. The matrix comparison and scalar kernel are ingredients, not substitutes for the full analytic lemmas.

## Manuscript results still in progress

- Optimized concavity and minimum attainment: `OptimizedConcavityStatement`.
- Joint convexity of the scalar deficit: `ScalarConvexityStatement`.
- The unrestricted block entropy inequality: `BlockEntropyStatement`.

These names in [Definitions.lean](../SchurEntropy/Definitions.lean) define propositions. They do not assert proofs or register axioms. The channel-capacity applications and entropic criteria have not yet been formalized in this repository.

## Build and audit

The project pins Lean `v4.34.0`, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, and the auxiliary matrix-calculus library `qubitStrongAdditivity` at commit `90e61c463deb42067c109c46f048c6374dfc5945`. The root Mathlib pin overrides the auxiliary library's declared version; the imported dependency chain has been compiled with this configuration.

With Lean's `elan` version manager installed, run:

```sh
lake exe cache get
lake build
lake build Mathlib.Util.AssertNoSorry
lake env lean Audit.lean
```

[Audit.lean](../Audit.lean) checks every imported declaration in the `SchurEntropy` namespace and rejects transitive axioms other than `propext`, `Classical.choice`, and `Quot.sound`. This includes rejection of `sorryAx`. It also prints the axioms of selected principal results. This audit checks proof dependencies; the result index above separately records whether the full manuscript statement has been proved.

See [third-party notices](../third_party/NOTICE) for the pinned dependency and adapted source excerpts.
