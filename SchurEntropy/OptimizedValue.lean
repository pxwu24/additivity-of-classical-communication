/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaDualValue.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.OptimizedMinimizer

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaEntropy

@[reducible] private local instance mNorm {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] private local instance mSpace {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (Matrix k k ℂ) := NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] private local instance mTop {k : Type*} [Fintype k] [DecidableEq k] :
    TopologicalSpace (Matrix k k ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] private local instance mAdd {k : Type*} [Fintype k] [DecidableEq k] :
    AddCommGroup (Matrix k k ℂ) := mNorm.toAddCommGroup
@[reducible] private local instance mModule {k : Type*} [Fintype k] [DecidableEq k] :
    Module ℝ (Matrix k k ℂ) := mSpace.toModule
@[reducible] private local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] private local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] private local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule


@[reducible] private local instance pAdd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    AddCommGroup (E × F) := Prod.normedAddCommGroup.toAddCommGroup
@[reducible] private local instance pTop {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    TopologicalSpace (E × F) := Prod.normedAddCommGroup.toUniformSpace.toTopologicalSpace
@[reducible] private local instance pModule {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] : Module ℝ (E × F) := Prod.normedSpace.toModule



variable {m : ℕ} {n : Fin m → ℕ}

def objectiveJointDerivative (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) (W : Blocks n) :
    (HermitianMat (BlockIndex n) ℂ × Blocks n) →L[ℝ] ℝ :=
  (-(psiGradient (J+diagonal W).mat)).comp (ContinuousLinearMap.fst ℝ _ _)+
    (gradient J lambda W).comp (ContinuousLinearMap.snd ℝ _ _)

theorem hasFDerivAt_jointObjective (lambda : Fin m → ℝ)
    {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n} (hW : W ∈ positiveInterior)
    (hT : (J+diagonal W).mat.PosDef) :
    HasFDerivAt (fun X : HermitianMat (BlockIndex n) ℂ × Blocks n => objective X.1 lambda X.2)
      (objectiveJointDerivative J lambda W) (J,W) := by
  let S := (diagonalCLM (n := n)).comp
    (ContinuousLinearMap.snd ℝ (HermitianMat (BlockIndex n) ℂ) (Blocks n))
  let L := (ContinuousLinearMap.fst ℝ (HermitianMat (BlockIndex n) ℂ) (Blocks n))+S
  have hdW := (hasFDerivAt_psi (A := diagonal W) (diagonal_posDef hW)).comp (J,W) S.hasFDerivAt
  have hdT := (hasFDerivAt_psi hT).comp (J,W) L.hasFDerivAt
  have hp := ((linearPenalty (n := n) lambda).comp
    (ContinuousLinearMap.snd ℝ (HermitianMat (BlockIndex n) ℂ) (Blocks n))).hasFDerivAt (x := (J,W))
  convert! (hdW.sub hdT).sub hp using 1
  · apply ContinuousLinearMap.ext
    intro X
    change -psiGradient (J+diagonal W).mat X.1+gradient J lambda W X.2 =
      psiGradient (diagonal W).mat (diagonal X.2)-
        psiGradient (J+diagonal W).mat (X.1+diagonal X.2)-linearPenalty lambda X.2
    rw [map_add]
    simp only [gradient]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,diagonalCLM_apply]
    ring

/-- The actual minimized term, with the certified global cone minimizer. -/
def minimumValue (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) : ℝ :=
  objective J lambda (minimizer J lambda)

def minimumValueGradient (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) :
    HermitianMat (BlockIndex n) ℂ →L[ℝ] ℝ := -psiGradient (J+diagonal (minimizer J lambda)).mat

/-- The envelope derivative follows from the real minimizer derivative and stationarity. -/
theorem hasFDerivAt_minimumValue {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    HasFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ => minimumValue K lambda)
      (minimumValueGradient J lambda) J := by
  have hW := minimizer_positiveInterior hJ hl
  have hd := (hasFDerivAt_jointObjective lambda hW
    (total_posDef hJ (interior_subset_cone hW))).comp J
    ((hasFDerivAt_id J).prodMk (hasStrictFDerivAt_minimizer hJ hl).hasFDerivAt)
  have hz : gradient J lambda (minimizer J lambda) = 0 := by
    rw [gradient_eq_blockPairing,minimizer_stationary hJ hl,map_zero]
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro H
  simp [objectiveJointDerivative,hz,minimumValueGradient]

theorem continuousAt_minimumValue {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    ContinuousAt (fun K : HermitianMat (BlockIndex n) ℂ => minimumValue K lambda) J :=
  (hasFDerivAt_minimumValue hJ hl).continuousAt

def totalDerivative (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) :
    HermitianMat (BlockIndex n) ℂ →L[ℝ] HermitianMat (BlockIndex n) ℂ :=
  ContinuousLinearMap.id ℝ _+(diagonalCLM (n := n)).comp (minimizerDerivative J lambda)

def minimumValueHessianRow (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (H : HermitianMat (BlockIndex n) ℂ) : HermitianMat (BlockIndex n) ℂ →L[ℝ] ℝ :=
  -(psiHessianRow (J+diagonal (minimizer J lambda)).mat H).comp
    (totalDerivative J lambda)

theorem hasFDerivAt_minimumValueGradient_row {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    HasFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ => minimumValueGradient K lambda H)
      (minimumValueHessianRow J lambda H) J := by
  have hW := minimizer_positiveInterior hJ hl
  have hd : HasFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ =>
      K+diagonal (minimizer K lambda)) (totalDerivative J lambda) J := by
    convert! (hasFDerivAt_id J).add ((diagonalCLM (n := n)).hasFDerivAt
      (x := minimizer J lambda) |>.comp J
        (hasStrictFDerivAt_minimizer hJ hl).hasFDerivAt) using 1
  convert! ((hasFDerivAt_psiGradient_row (total_posDef hJ (interior_subset_cone hW)) H).comp J hd).neg using 1

/-- Pinching all diagonal blocks, as an actual real continuous linear map. -/
def pinching : HermitianMat (BlockIndex n) ℂ →L[ℝ] HermitianMat (BlockIndex n) ℂ := (diagonalCLM (n := n)).comp (pinchCLM (n := n))

theorem pinching_posDef {J : HermitianMat (BlockIndex n) ℂ} (hJ : J.mat.PosDef) :
    (pinching J).mat.PosDef := by
  apply diagonal_posDef
  intro i
  exact hJ.submatrix (@sigma_mk_injective (Fin m) (fun i => Fin (n i)) i)

/-- The manuscript's complete minimized dual value. -/
def value (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) : ℝ :=
  psi (pinching J)+minimumValue J lambda

def valueGradient (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) :
    HermitianMat (BlockIndex n) ℂ →L[ℝ] ℝ :=
  (psiGradient (pinching J).mat).comp (pinching (n := n))+minimumValueGradient J lambda

theorem hasFDerivAt_value {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    HasFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ => value K lambda)
      (valueGradient J lambda) J :=
  ((hasFDerivAt_psi (pinching_posDef hJ)).comp J (pinching (n := n)).hasFDerivAt).add
    (hasFDerivAt_minimumValue hJ hl)

def valueHessianRow (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (H : HermitianMat (BlockIndex n) ℂ) : HermitianMat (BlockIndex n) ℂ →L[ℝ] ℝ :=
  (psiHessianRow (pinching J).mat (pinching H)).comp (pinching (n := n))+
    minimumValueHessianRow J lambda H

/-- The actual value Hessian before identifying the Schur expression. -/
theorem hasFDerivAt_valueGradient_row {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (H : HermitianMat (BlockIndex n) ℂ) :
    HasFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ => valueGradient K lambda H)
      (valueHessianRow J lambda H) J := by
  have hd := (hasFDerivAt_psiGradient_row (pinching_posDef hJ) (pinching H)).comp J (pinching (n := n)).hasFDerivAt
  convert! hd.add (hasFDerivAt_minimumValueGradient_row hJ hl H) using 1

theorem continuousAt_value {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    ContinuousAt (fun K : HermitianMat (BlockIndex n) ℂ => value K lambda) J :=
  (hasFDerivAt_value hJ hl).continuousAt

end SchurEntropy.Optimized
