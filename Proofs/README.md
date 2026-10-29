# Proofs of the manuscript results

These notes collect the mathematical proofs corresponding to the numbered
results in **“Classical communication over quantum channels: does entanglement
help in nature?”**, using the updated PDF's numbering. They include the
normalization, support, and boundary details needed in singular cases.

The supplied [manuscript PDF](Manuscript.pdf) is preserved as provided. The
Markdown proofs supply the detailed arguments and corrections discussed
alongside the formalization, while retaining the PDF's result numbering.

| Manuscript result | Mathematical proof | Lean proof |
| --- | --- | --- |
| Lemma 2.1 — Entropic criterion for strong additivity | [Entropic criteria](entropic-criteria.md) | [StandardCriterion.lean](../Lean/SchurEntropy/Capacity/StandardCriterion.lean) |
| Proposition 2.2 — Weaker entropic criterion for strong additivity | [Entropic criteria](entropic-criteria.md) | [OutputCenterCriterion.lean](../Lean/SchurEntropy/Capacity/OutputCenterCriterion.lean) |
| Theorem 3.1 — Schur-weighted block entropy inequality | [Block entropy inequality](block-entropy.md) | [Results.lean](../Lean/SchurEntropy/Results.lean) |
| Lemma 3.2 — Concavity and attainment of the optimized entropy deficit | [Analytic lemmas](analytic-lemmas.md) | [OptimizedBridge.lean](../Lean/SchurEntropy/OptimizedBridge.lean) |
| Lemma 3.3 — Joint convexity of the scalar entropy deficit | [Analytic lemmas](analytic-lemmas.md) | [ScalarConvexity.lean](../Lean/SchurEntropy/ScalarConvexity.lean) |
| Lemma 4.1 — Phase-covariant normal form | [Phase-covariant channels](phase-covariant.md) | [NormalForm.lean](../Lean/SchurEntropy/PhaseCovariant/NormalForm.lean) |
| Theorem 4.2 — Strong additivity for all phase-covariant channels | [Phase-covariant channels](phase-covariant.md) | [PhaseCovariant/Results.lean](../Lean/SchurEntropy/PhaseCovariant/Results.lean) |
| Lemma 5.1 — Qubit-output Kraus decomposition | [Qubit-output channels](qubit-channels.md) | [DecompositionGeneral.lean](../Lean/SchurEntropy/Qubit/DecompositionGeneral.lean) |
| Theorem 5.2 — Strong additivity for a class of qubit-output channels, including all qubit-to-qubit channels | [Qubit-output channels](qubit-channels.md) | [Qubit/Results.lean](../Lean/SchurEntropy/Qubit/Results.lean) |

The proof of Theorem 3.1 uses Lemmas 3.2 and 3.3. Theorem 4.2 combines that
inequality with Proposition 2.2; Theorem 5.2 combines it with Lemma 2.1 and
the decomposition in Lemma 5.1 when the input is a qubit. The analytic-lemma
notes identify the supporting matrix estimates and their verified Lean
sources.

The discussion's extension to multiple coherent Kraus operators and its
low-dimensional threshold problem remain open directions. No proof of
these open statements is claimed. The classical-capacity coding theorem
and regularization formula are cited background.

See [Lean Formalization](../README.md#lean-formalization) for the result-to-code
table, and [verification details](../Lean/verification.md) for the build,
axiom audit, and exact formalization scope.
