/-
Adapted for arbitrary finite block families from BetaValueHessian.lean
in KitaKen1/qubit-strong-additivity, commit 90e61c463deb42067c109c46f048c6374dfc5945.
The upstream source is distributed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/
import SchurEntropy.OptimizedValue
import SchurEntropy.MultiBlockHessian
import SchurEntropy.MultiBlockCoordinates

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaPowers QubitAdditivity.BetaEntropy
open QubitAdditivity.BetaDualDerivative (logHermDeriv logHermDeriv_mat hasStrictFDerivAt_hermLog)
open BlockAlgebra (blockInclusion DiagonalUnitIndex)

@[reducible] local instance hessianMNorm {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance hessianMSpace {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (Matrix k k ℂ) := NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] local instance hessianMTop {k : Type*} [Fintype k] [DecidableEq k] :
    TopologicalSpace (Matrix k k ℂ) := hessianMNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance hessianMAdd {k : Type*} [Fintype k] [DecidableEq k] :
    AddCommGroup (Matrix k k ℂ) := hessianMNorm.toAddCommGroup
@[reducible] local instance hessianMModule {k : Type*} [Fintype k] [DecidableEq k] :
    Module ℝ (Matrix k k ℂ) := hessianMSpace.toModule
@[reducible] local instance hessianHTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hessianHAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hessianHModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule


@[reducible] local instance hessianPAdd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    AddCommGroup (E × F) := Prod.normedAddCommGroup.toAddCommGroup
@[reducible] local instance hessianPTop {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    TopologicalSpace (E × F) := Prod.normedAddCommGroup.toUniformSpace.toTopologicalSpace
@[reducible] local instance hessianPModule {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] : Module ℝ (E × F) := Prod.normedSpace.toModule



variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m : ℕ} {n : Fin m → ℕ}
local notation "V" => blockInclusion n

def vector (H : HermitianMat ι ℂ) : ι × ι → ℂ := MultiBlock.vector H.mat

def blockVector (H : Blocks n) : DiagonalUnitIndex n → ℂ :=
  MultiBlock.blockVector n (fun i => (H i).mat)

def blockLogDeriv (W : Blocks n) : Blocks n →L[ℝ] Blocks n :=
  ContinuousLinearMap.pi (fun i => (logHermDeriv (W i)).comp (ContinuousLinearMap.proj i))

theorem vector_diagonal (H : Blocks n) : vector (diagonal H) = V *ᵥ blockVector H :=
  MultiBlock.vector_diagonal n (fun i => (H i).mat)

theorem vector_pinch (H : HermitianMat (BlockIndex n) ℂ) : blockVector (pinchCLM H) = Vᴴ *ᵥ vector H :=
  MultiBlock.vector_pinch n H.mat

theorem vector_logHermDeriv {A : HermitianMat ι ℂ} (hA : A.mat.PosDef) (H : HermitianMat ι ℂ) :
    vector (logHermDeriv A H) = (km A.mat)⁻¹ *ᵥ vector H := by
  ext ij
  exact congrFun (congrFun (logHermDeriv_mat hA H) ij.1) ij.2

theorem blockKM_inv {W : Blocks n} (hW : W ∈ positiveInterior) :
    (MultiBlock.blockKM n (fun i => (W i).mat))⁻¹ =
      Matrix.blockDiagonal' (fun i => (km (W i).mat)⁻¹) :=
  MultiBlock.diagonal_inv _ (fun i => (BetaKM.km_posDef (hW i)).isUnit)

theorem vector_blockLogDeriv {W : Blocks n} (hW : W ∈ positiveInterior) (H : Blocks n) :
    blockVector (blockLogDeriv W H) =
      (MultiBlock.blockKM n (fun i => (W i).mat))⁻¹ *ᵥ blockVector H := by
  rw [blockKM_inv hW]
  ext ⟨i, a, b⟩
  rw [MultiBlock.diagonal_mulVec]
  exact congrFun (vector_logHermDeriv (hW i) (H i)) (a, b)

theorem logHermDeriv_diagonal {W : Blocks n} (hW : W ∈ positiveInterior) (H : Blocks n) :
    logHermDeriv (diagonal W) (diagonal H) = diagonal (blockLogDeriv W H) := by
  have hd₁ := (hasStrictFDerivAt_hermLog (diagonal_posDef hW)).hasFDerivAt.comp W
    (diagonalCLM (n := n)).hasFDerivAt
  have hdblock : HasFDerivAt (fun Z : Blocks n => fun i => BetaDual.hermLog (Z i))
      (blockLogDeriv W) W := by
    apply hasFDerivAt_pi.2
    intro i
    let P : Blocks n →L[ℝ] HermitianMat (Fin (n i)) ℂ := ContinuousLinearMap.proj i
    exact (hasStrictFDerivAt_hermLog (hW i)).hasFDerivAt.comp W
      P.hasFDerivAt
  have hd₂ := (diagonalCLM (n := n)).hasFDerivAt.comp W hdblock
  have hd₂' : HasFDerivAt (fun Z : Blocks n => BetaDual.hermLog (diagonal Z))
      ((diagonalCLM (n := n)).comp (blockLogDeriv W)) W := by
    convert! hd₂ using 1
    funext Z
    exact hermLog_diagonal Z
  exact congrArg (fun L : Blocks n →L[ℝ] HermitianMat (BlockIndex n) ℂ => L H) (hd₁.unique hd₂')

omit [Fintype ι] in
@[simp] theorem vector_add (H K : HermitianMat ι ℂ) : vector (H+K) = vector H+vector K := rfl
@[simp] theorem blockVector_sub (H K : Blocks n) : blockVector (H-K) = blockVector H-blockVector K := rfl

theorem vector_residualDerivative {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hW : W ∈ positiveInterior) (hT : (J+diagonal W).mat.PosDef) (H : Blocks n) :
    blockVector (residualDerivative J W H) =
      ((MultiBlock.blockKM n (fun i => (W i).mat))⁻¹ -
        Vᴴ * (km (J+diagonal W).mat)⁻¹ * V) *ᵥ blockVector H := by
  change blockVector (pinchCLM (logHermDeriv (diagonal W) (diagonal H) -
    logHermDeriv (J+diagonal W) (diagonal H))) = _
  rw [map_sub, logHermDeriv_diagonal hW]
  change blockVector (pinch (diagonal (blockLogDeriv W H)) -
    pinchCLM (logHermDeriv (J+diagonal W) (diagonal H))) = _
  rw [pinch_diagonal, blockVector_sub, vector_blockLogDeriv hW, vector_pinch,
    vector_logHermDeriv hT, vector_diagonal]
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]

theorem minimizerDerivative_equation {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    residualDerivative J (minimizer J lambda) (minimizerDerivative J lambda H) =
      pinchCLM (logHermDeriv (J+diagonal (minimizer J lambda)) H) := by
  have hW := minimizer_positiveInterior hJ hl
  have hi := residualDerivative_isInvertible hJ hW
  change residualDerivative J (minimizer J lambda)
    (-((residualDerivative J (minimizer J lambda)).inverse
      (-pinchCLM (logHermDeriv (J+diagonal (minimizer J lambda)) H)))) = _
  rw [map_neg, hi.self_apply_inverse, neg_neg]

theorem total_gap_posDef {J : HermitianMat (BlockIndex n) ℂ} (hJ : J.mat.PosDef) (W : Blocks n) :
    ((J+diagonal W).mat-Matrix.blockDiagonal' (fun i => (W i).mat)).PosDef := by
  simpa only [HermitianMat.mat_add, diagonal_mat, add_sub_cancel_right] using hJ

theorem vector_minimizerDerivative {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    blockVector (minimizerDerivative J lambda H) =
      ((MultiBlock.blockKM n (fun i => (minimizer J lambda i).mat))⁻¹-
        Vᴴ*(km (J+diagonal (minimizer J lambda)).mat)⁻¹*V)⁻¹ *ᵥ
        (Vᴴ *ᵥ ((km (J+diagonal (minimizer J lambda)).mat)⁻¹ *ᵥ vector H)) := by
  let W := minimizer J lambda
  let E := (MultiBlock.blockKM n (fun i => (W i).mat))⁻¹ - Vᴴ*(km (J+diagonal W).mat)⁻¹*V
  have hW := minimizer_positiveInterior hJ hl
  have hT := total_posDef hJ (interior_subset_cone hW)
  have hE : E.PosDef := MultiBlock.inverseKM_compression_gap_posDef n hT hW (total_gap_posDef hJ W)
  have he := congrArg blockVector (minimizerDerivative_equation hJ hl H)
  rw [vector_residualDerivative hW hT, vector_pinch, vector_logHermDeriv hT] at he
  change E *ᵥ blockVector (minimizerDerivative J lambda H) = _ at he
  have hinv : E⁻¹*E = 1 := Matrix.nonsing_inv_mul E ((Matrix.isUnit_iff_isUnit_det E).mp hE.isUnit)
  change blockVector (minimizerDerivative J lambda H) = E⁻¹ *ᵥ _
  rw [← he, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

theorem vector_totalDerivative {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    vector (totalDerivative J lambda H) = vector H+
      V *ᵥ (((MultiBlock.blockKM n (fun i => (minimizer J lambda i).mat))⁻¹-
        Vᴴ*(km (J+diagonal (minimizer J lambda)).mat)⁻¹*V)⁻¹ *ᵥ
        (Vᴴ *ᵥ ((km (J+diagonal (minimizer J lambda)).mat)⁻¹ *ᵥ vector H))) := by
  change vector (H+diagonal (minimizerDerivative J lambda H)) = _
  rw [vector_add, vector_diagonal, vector_minimizerDerivative hJ hl]

theorem vector_pinching (H : HermitianMat (BlockIndex n) ℂ) :
    vector (pinching H) = V *ᵥ (Vᴴ *ᵥ vector H) := by
  change vector (diagonal (pinchCLM H)) = _
  rw [vector_diagonal, vector_pinch]

private theorem block_pairing_lift (x y : DiagonalUnitIndex n → ℂ) :
    star (V *ᵥ x) ⬝ᵥ (V *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    BlockAlgebra.blockInclusion_isometry, Matrix.one_mulVec]

theorem pinched_psiHessianRow_eq_pairing {J : HermitianMat (BlockIndex n) ℂ} (hJ : J.mat.PosDef)
    (H K : HermitianMat (BlockIndex n) ℂ) :
    psiHessianRow (pinching J).mat (pinching H) (pinching K) =
      (BetaComparison.pairing (vector H)
        (V*(MultiBlock.blockKM n (fun i => (pinch J i).mat))⁻¹*Vᴴ) (vector K)).re := by
  have hP : pinch J ∈ positiveInterior := fun i => hJ.submatrix (@sigma_mk_injective (Fin m) (fun j => Fin (n j)) i)
  rw [psiHessianRow_apply, ← logHermDeriv_mat (pinching_posDef hJ), trace_mul_eq_vector_pairing]
  change (star (vector (pinching H)) ⬝ᵥ vector (logHermDeriv (pinching J) (pinching K))).re = _
  have he : vector (logHermDeriv (pinching J) (pinching K)) =
      V *ᵥ ((MultiBlock.blockKM n (fun i => (pinch J i).mat))⁻¹ *ᵥ (Vᴴ *ᵥ vector K)) := by
    change vector (logHermDeriv (diagonal (pinchCLM J)) (diagonal (pinchCLM K))) = _
    rw [logHermDeriv_diagonal (W := pinchCLM J) hP, vector_diagonal,
      vector_blockLogDeriv (W := pinchCLM J) hP, vector_pinch]
    rfl
  rw [vector_pinching, he, block_pairing_lift, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [BetaComparison.pairing, ← Matrix.mulVec_mulVec, Matrix.conjTranspose_conjTranspose]

theorem gapKM_total (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :
    MultiBlock.blockKM n (MultiBlock.gap n (J+diagonal W).mat (fun i => (W i).mat)) =
      MultiBlock.blockKM n (fun i => (pinch J i).mat) := by
  congr 1
  funext i
  ext a b
  simp [MultiBlock.gap, BlockAlgebra.diagonalBlock, diagonal_mat, pinch, Matrix.submatrix_apply]
  rfl

def eliminatedMatrix (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :=
  V*(MultiBlock.blockKM n (MultiBlock.gap n (J+diagonal W).mat (fun i => (W i).mat)))⁻¹*Vᴴ-
    (km (J+diagonal W).mat)⁻¹-
    (km (J+diagonal W).mat)⁻¹*V*
      ((MultiBlock.blockKM n (fun i => (W i).mat))⁻¹-
        Vᴴ*(km (J+diagonal W).mat)⁻¹*V)⁻¹*Vᴴ*(km (J+diagonal W).mat)⁻¹

theorem valueHessianRow_eq_eliminated_pairing {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H K : HermitianMat (BlockIndex n) ℂ) :
    valueHessianRow J lambda H K =
      (BetaComparison.pairing (vector H) (eliminatedMatrix J (minimizer J lambda)) (vector K)).re := by
  change psiHessianRow (pinching J).mat (pinching H) (pinching K) -
    psiHessianRow (J+diagonal (minimizer J lambda)).mat H (totalDerivative J lambda K) = _
  rw [pinched_psiHessianRow_eq_pairing hJ, psiHessianRow_eq_pairing]
  change (BetaComparison.pairing (vector H)
    (V*(MultiBlock.blockKM n (fun i => (pinch J i).mat))⁻¹*Vᴴ) (vector K)).re -
    (BetaComparison.pairing (vector H) (km (J+diagonal (minimizer J lambda)).mat)⁻¹
      (vector (totalDerivative J lambda K))).re = _
  rw [vector_totalDerivative hJ hl]
  simp only [eliminatedMatrix, gapKM_total, BetaComparison.pairing, Matrix.sub_mulVec,
    Matrix.mulVec_add, ← Matrix.mulVec_mulVec, dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]
  ring

theorem valueHessianRow_self_nonpos {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    valueHessianRow J lambda H H ≤ 0 := by
  let W := minimizer J lambda
  have hW := minimizer_positiveInterior hJ hl
  have hs (i : Fin m) : logarithm (W i).mat =
      BlockAlgebra.diagonalBlock n (logarithm (J+diagonal W).mat) i + (lambda i : ℂ) • 1 := by
    have hz := congrArg (fun Z : Blocks n => (Z i).mat) (minimizer_stationary hJ hl)
    change logarithm (W i).mat -
      BlockAlgebra.diagonalBlock n (logarithm (J+diagonal W).mat) i - (lambda i : ℝ) • 1 = 0 at hz
    rw [BetaDual.real_smul_identity, sub_sub] at hz
    exact sub_eq_zero.mp hz
  have hm : eliminatedMatrix J W ≤ 0 := MultiBlock.eliminated_expression_nonpos n
    (total_posDef hJ (interior_subset_cone hW)) hW (total_gap_posDef hJ W)
    (fun i => (lambda i : ℂ)) hs
  rw [valueHessianRow_eq_eliminated_pairing hJ hl]
  simpa [BetaComparison.quadratic, BetaComparison.pairing] using
    BetaComparison.quadratic_mono hm (vector H)

end SchurEntropy.Optimized
