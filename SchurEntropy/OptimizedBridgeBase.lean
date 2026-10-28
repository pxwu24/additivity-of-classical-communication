import SchurEntropy.Definitions
import SchurEntropy.OptimizedDefinitions

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy
open QubitAdditivity QubitAdditivity.BetaEntropy

variable {m : ℕ} {n : Fin m → ℕ}

theorem psi_eq_neg_entropy_bits {k : Type*} [Fintype k] [DecidableEq k]
    (A : HermitianMat k ℂ) : psi A = -entropy A.mat * Real.log 2 := by
  unfold psi entropy OpenAIEntropy.entropy
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

theorem diagonal_pinch_mat (J : HermitianMat (BlockIndex n) ℂ) :
    (Optimized.diagonal (Optimized.pinch J)).mat = pinching n J.mat := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change Matrix.blockDiagonal' (fun k => J.mat.submatrix (Sigma.mk k) (Sigma.mk k))
    ⟨i, a⟩ ⟨j, b⟩ = pinching n J.mat ⟨i, a⟩ ⟨j, b⟩
  obtain rfl | hij := eq_or_ne i j
  · simp [Matrix.blockDiagonal'_apply, Matrix.submatrix_apply, pinching_apply]
  · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hij, pinching_apply, hij]

theorem diagonal_admissible {W : Optimized.Blocks n}
    (hW : W ∈ Optimized.positiveCone) :
    (Optimized.diagonal W).mat ∈ admissibleNoise n := by
  refine ⟨Optimized.diagonal_posSemidef hW, ?_⟩
  rw [IsBlockDiagonal, ← diagonal_pinch_mat, Optimized.pinch_diagonal]

theorem pinch_mem_positiveCone {W : HermitianMat (BlockIndex n) ℂ}
    (hW : W.mat.PosSemidef) : Optimized.pinch W ∈ Optimized.positiveCone :=
  fun i => hW.submatrix (Sigma.mk i)

theorem blockTrace_diagonal (W : Optimized.Blocks n) (i : Fin m) :
    blockTrace n (Optimized.diagonal W).mat i = (W i).mat.trace.re := by
  change (∑ a : Fin (n i),
    (Matrix.blockDiagonal' (fun j => (W j).mat) ⟨i, a⟩ ⟨i, a⟩).re) = _
  simp [Matrix.blockDiagonal'_apply, Matrix.trace, Matrix.diag_apply]

/-- Natural-log multiplier corresponding to the multiplier in the bit-entropy
objective. Multiplication by `log 2` preserves strict negativity. -/
def naturalMultiplier (μ : Fin m → ℝ) : Fin m → ℝ := fun i => μ i * Real.log 2

theorem naturalMultiplier_neg {μ : Fin m → ℝ} (hμ : ∀ i, μ i < 0) :
    ∀ i, naturalMultiplier μ i < 0 :=
  fun i => mul_neg_of_neg_of_pos (hμ i) (Real.log_pos (by norm_num))

theorem naturalPenalty_eq (μ : Fin m → ℝ) (W : Optimized.Blocks n) :
    Optimized.linearPenalty (naturalMultiplier μ) W =
      dot μ (blockTrace n (Optimized.diagonal W).mat) * Real.log 2 := by
  simp only [Optimized.linearPenalty_apply, naturalMultiplier, dot,
    blockTrace_diagonal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact conversion of the optimized objective from natural logs to bits. -/
theorem dualCost_diagonal_eq (μ : Fin m → ℝ)
    (J : HermitianMat (BlockIndex n) ℂ) (W : Optimized.Blocks n) :
    dualCost n μ J.mat (Optimized.diagonal W).mat =
      (psi (Optimized.diagonal (Optimized.pinch J)) +
        Optimized.objective J (naturalMultiplier μ) W) / Real.log 2 := by
  rw [dualCost_eq, Optimized.objective, naturalPenalty_eq]
  simp only [psi_eq_neg_entropy_bits, diagonal_pinch_mat, HermitianMat.mat_add]
  unfold deficit
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

/-- Any true minimizer in block coordinates is also a true minimizer among
all admissible block diagonal matrices. -/
theorem dualCost_minimal_of_block_minimal
    (μ : Fin m → ℝ) (J : HermitianMat (BlockIndex n) ℂ)
    (W : Optimized.Blocks n)
    (hmin : IsMinOn (Optimized.objective J (naturalMultiplier μ))
      Optimized.positiveCone W) :
    ∀ Z ∈ admissibleNoise n,
      dualCost n μ J.mat (Optimized.diagonal W).mat ≤ dualCost n μ J.mat Z := by
  intro Z hZ
  let z : HermitianMat (BlockIndex n) ℂ := ⟨Z, hZ.1.isHermitian⟩
  have hz : (Optimized.diagonal (Optimized.pinch z)).mat = Z :=
    (diagonal_pinch_mat z).trans hZ.2
  have hi := hmin (pinch_mem_positiveCone (W := z) hZ.1)
  change Optimized.objective J (naturalMultiplier μ) W ≤
    Optimized.objective J (naturalMultiplier μ) (Optimized.pinch z) at hi
  conv_rhs => rw [← hz]
  rw [dualCost_diagonal_eq, dualCost_diagonal_eq]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  linarith

/-- Attainment identifies the literal `sInf` definition; no boundedness of an
unproved infimum is silently assumed. -/
theorem optimizedDeficit_eq_of_block_minimal
    (μ : Fin m → ℝ) (J : HermitianMat (BlockIndex n) ℂ)
    (W : Optimized.Blocks n) (hW : W ∈ Optimized.positiveCone)
    (hmin : IsMinOn (Optimized.objective J (naturalMultiplier μ))
      Optimized.positiveCone W) :
    optimizedDeficit n μ J.mat = dualCost n μ J.mat (Optimized.diagonal W).mat := by
  have his : IsLeast ((dualCost n μ J.mat) '' admissibleNoise n)
      (dualCost n μ J.mat (Optimized.diagonal W).mat) := by
    refine ⟨⟨(Optimized.diagonal W).mat, diagonal_admissible hW, rfl⟩, ?_⟩
    rintro _ ⟨Z, hZ, rfl⟩
    exact dualCost_minimal_of_block_minimal μ J W hmin Z hZ
  exact his.csInf_eq

/-- Transport a Hermitian-coordinate concavity theorem through the exact
positive base conversion to the original matrix cone. -/
theorem concaveOn_optimizedDeficit_of_value (μ : Fin m → ℝ)
    (g : HermitianMat (BlockIndex n) ℂ → ℝ)
    (hg : ConcaveOn ℝ {J : HermitianMat (BlockIndex n) ℂ | J.mat.PosSemidef} g)
    (heq : ∀ (J : HermitianMat (BlockIndex n) ℂ), J.mat.PosSemidef →
      optimizedDeficit n μ J.mat = g J / Real.log 2) :
    ConcaveOn ℝ {J : BlockMatrix n | J.PosSemidef} (optimizedDeficit n μ) := by
  constructor
  · intro J hJ K hK a b ha hb hab
    exact (hJ.smul ha).add (hK.smul hb)
  intro J hJ K hK a b ha hb hab
  let j : HermitianMat (BlockIndex n) ℂ := ⟨J, hJ.isHermitian⟩
  let k : HermitianMat (BlockIndex n) ℂ := ⟨K, hK.isHermitian⟩
  have hmix : (a • j + b • k).mat.PosSemidef := by
    convert! (hJ.smul ha).add (hK.smul hb) using 1
  have heJ := heq j hJ
  have heK := heq k hK
  have heMix := heq (a • j + b • k) hmix
  change optimizedDeficit n μ J = _ at heJ
  change optimizedDeficit n μ K = _ at heK
  change optimizedDeficit n μ (a • J + b • K) = _ at heMix
  rw [heJ, heK, heMix]
  have hi := hg.2 (x := j) (y := k) hJ hK ha hb hab
  have hd := div_le_div_of_nonneg_right hi (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  simp only [smul_eq_mul] at hd ⊢
  convert hd using 1
  ring

end SchurEntropy
