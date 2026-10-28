# Lean source organization

[Definitions.lean](Definitions.lean) defines spectral entropy in bits, block pinching, Schur multiplication, scalar skeletons, and the three exact manuscript propositions.

The checked modules are collected by [SchurEntropy.lean](../SchurEntropy.lean). The complete rank-one proof is [RankOneInequality.lean](RankOneInequality.lean); its supporting modules handle isometries, zero block traces, orthogonal entropy addition, and monotonicity of entropy increments. [BlockReduction.lean](BlockReduction.lean) proves the finite-sum reduction with its outstanding analytic hypotheses explicit.

`MultiBlock*.lean` develops the arbitrary-block matrix comparison needed for optimized concavity. [ScalarKernel.lean](ScalarKernel.lean) proves the logarithmic-mean sum-of-squares certificate needed for scalar joint convexity.

See the [verification index](../docs/verification.md) for exact checked declarations, remaining obligations, build instructions, and the axiom audit. The channel-capacity and entropic-criterion modules remain future work.
