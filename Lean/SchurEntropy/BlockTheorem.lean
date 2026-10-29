import SchurEntropy.BlockReduction
import SchurEntropy.SupportingMultiplier
import SchurEntropy.BlockBoundary

/-!
# Block entropy from the two analytic lemmas

The rank-one inequality, spectral decomposition, negative supporting multiplier,
and passage to singular matrices are proved in the imported modules. This file
assembles the manuscript's general theorem with precisely its two analytic
lemmas as hypotheses.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy

/-- Positive definiteness gives strictly positive traces on nonempty blocks. -/
theorem blockTrace_pos {m : ℕ} {n : Fin m → ℕ}
    (hn : ∀ i, 0 < n i) {H : BlockMatrix n} (hH : H.PosDef) (i : Fin m) :
    0 < blockTrace n H i := by
  let : Nonempty (Fin (n i)) := ⟨⟨0, hn i⟩⟩
  exact Finset.sum_pos (fun a _ =>
    (Complex.pos_iff.mp (hH.diag_pos (i := ⟨i, a⟩))).1) Finset.univ_nonempty

/-- For positive definite data, the two analytic lemmas imply the desired
comparison using the strictly negative derivative in the noise variable. -/
theorem blockEntropy_posDef_of_two_lemmas
    (hOptimized : OptimizedConcavityStatement)
    (hScalar : ScalarConvexityStatement)
    {m : ℕ} (n : Fin m → ℕ) (hm : 0 < m) (hn : ∀ i, 0 < n i)
    (C : Matrix (Fin m) (Fin m) ℂ) (H W : BlockMatrix n)
    (hC : C.PosDef) (hH : H.PosDef) (hW : W.PosDef)
    (hWD : IsBlockDiagonal n W) :
    scalarFunction C (blockTrace n H) (blockTrace n W) ≤
      deficit n (blockSchur C H) W := by
  obtain ⟨μ, hμ, hs⟩ := SupportingMultiplier.exists_negative_support hScalar hm C hC
    (blockTrace n H) (blockTrace_pos hn hH) (blockTrace n W) (blockTrace_pos hn hW)
  exact blockEntropy_of_analytic_inputs hOptimized hScalar n hm hn C hC.posSemidef
    H W hH.posSemidef ⟨hW.posSemidef, hWD⟩ μ hμ hs

/-- The full block-entropy theorem follows from the optimized-deficit concavity
and scalar joint convexity lemmas, including singular matrices and zero traces. -/
theorem blockEntropy_of_two_lemmas
    (hOptimized : OptimizedConcavityStatement)
    (hScalar : ScalarConvexityStatement) : BlockEntropyStatement := by
  intro m n C H W hm hn hC hH hW hWD
  exact blockEntropy_of_posDef n
    (fun C H W hC hH hW hWD =>
      blockEntropy_posDef_of_two_lemmas hOptimized hScalar n hm hn C H W hC hH hW hWD)
    C H W hC hH hW hWD

end SchurEntropy
