import SchurEntropy.OptimizedBridgeBase
import SchurEntropy.OptimizedBoundary

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy

variable {m : ℕ} {n : Fin m → ℕ}

/-- The spectral-entropy infimum in bits is precisely the proved natural-log
minimum value divided by `log 2`. -/
theorem optimizedDeficit_eq_value (μ : Fin m → ℝ)
    (J : HermitianMat (BlockIndex n) ℂ) (hJ : J.mat.PosSemidef)
    (hμ : ∀ i, μ i < 0) :
    optimizedDeficit n μ J.mat =
      Optimized.value J (naturalMultiplier μ) / Real.log 2 := by
  have hs := Optimized.minimizer_spec_psd hJ (naturalMultiplier_neg hμ)
  rw [optimizedDeficit_eq_of_block_minimal μ J _ hs.1 hs.2, dualCost_diagonal_eq]
  rfl

/-- The minimum is attained in the original matrix domain, including for
singular input matrices. -/
theorem optimizedDeficit_attained (μ : Fin m → ℝ) (hμ : ∀ i, μ i < 0)
    (J : BlockMatrix n) (hJ : J.PosSemidef) :
    ∃ W ∈ admissibleNoise n,
      optimizedDeficit n μ J = dualCost n μ J W ∧
      ∀ Z ∈ admissibleNoise n, dualCost n μ J W ≤ dualCost n μ J Z := by
  let j : HermitianMat (BlockIndex n) ℂ := ⟨J, hJ.isHermitian⟩
  let w := Optimized.minimizer j (naturalMultiplier μ)
  have hs := Optimized.minimizer_spec_psd (J := j) hJ (naturalMultiplier_neg hμ)
  refine ⟨(Optimized.diagonal w).mat, diagonal_admissible hs.1, ?_, ?_⟩
  · exact optimizedDeficit_eq_of_block_minimal μ j w hs.1 hs.2
  · exact dualCost_minimal_of_block_minimal μ j w hs.2

/-- Concavity of the literal `sInf`-defined bit-entropy value on the complete
positive semidefinite matrix cone. -/
theorem concaveOn_optimizedDeficit (μ : Fin m → ℝ) (hμ : ∀ i, μ i < 0) :
    ConcaveOn ℝ {J : BlockMatrix n | J.PosSemidef} (optimizedDeficit n μ) := by
  exact concaveOn_optimizedDeficit_of_value μ
    (fun J => Optimized.value J (naturalMultiplier μ))
    (Optimized.concaveOn_value_psd (naturalMultiplier_neg hμ))
    (fun J hJ => optimizedDeficit_eq_value μ J hJ hμ)

/-- The complete optimized concavity lemma, with attainment and all boundary
cases, for the manuscript's genuine von Neumann entropy in bits. -/
theorem optimizedConcavity : OptimizedConcavityStatement := by
  intro m n μ _hm _hn hμ
  exact ⟨optimizedDeficit_attained μ hμ, concaveOn_optimizedDeficit μ hμ⟩

end SchurEntropy
