/-
Adapted for arbitrary finite block families from BetaDualDerivative.lean
in KitaKen1/qubit-strong-additivity, commit 90e61c463deb42067c109c46f048c6374dfc5945.
The upstream source is distributed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/
import SchurEntropy.OptimizedConvex
import QubitAdditivity.BetaDualDerivative

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology RealInnerProductSpace

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaEntropy
open QubitAdditivity.BetaDualDerivative (logHermDeriv hasStrictFDerivAt_hermLog logHermDeriv_mat)

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

theorem hermLog_diagonal (W : Blocks n) :
    BetaDual.hermLog (diagonal W) = diagonal (fun i => BetaDual.hermLog (W i)) := by
  apply HermitianMat.ext
  exact logarithm_diagonal W

theorem stationaryResidual_eq (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (W : Blocks n) : stationaryResidual J lambda W =
      pinch (BetaDual.hermLog (diagonal W))-pinch (BetaDual.hermLog (J+diagonal W))-
        (fun i => lambda i • 1) := by
  rw [hermLog_diagonal, pinch_diagonal]
  rfl

def residualDerivative (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) : Blocks n →L[ℝ] Blocks n :=
  (pinchCLM (n := n)).comp ((logHermDeriv (diagonal W)-logHermDeriv (J+diagonal W)).comp (diagonalCLM (n := n)))

def parameterDerivative (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :
    HermitianMat (BlockIndex n) ℂ →L[ℝ] Blocks n := -(pinchCLM (n := n)).comp (logHermDeriv (J+diagonal W))

def jointDerivative (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :
    (HermitianMat (BlockIndex n) ℂ × Blocks n) →L[ℝ] Blocks n :=
  (parameterDerivative J W).comp (ContinuousLinearMap.fst ℝ _ _)+
    (residualDerivative J W).comp (ContinuousLinearMap.snd ℝ _ _)

theorem hasStrictFDerivAt_stationaryResidual {J : HermitianMat (BlockIndex n) ℂ}
    (lambda : Fin m → ℝ) {W : Blocks n} (hW : W ∈ positiveInterior)
    (hT : (J+diagonal W).mat.PosDef) :
    HasStrictFDerivAt (stationaryResidual J lambda) (residualDerivative J W) W := by
  have hw := (hasStrictFDerivAt_hermLog (diagonal_posDef hW)).comp W
    (diagonalCLM (n := n)).hasStrictFDerivAt
  have hl := (diagonalCLM (n := n)).hasStrictFDerivAt (x := W) |>.const_add J
  have ht := (hasStrictFDerivAt_hermLog hT).comp W hl
  have hp := (pinchCLM (n := n)).hasStrictFDerivAt.comp W (hw.sub ht)
  convert! hp.sub_const (fun i => lambda i • (1 : HermitianMat (Fin (n i)) ℂ)) using 1
  · funext Z
    rw [stationaryResidual_eq]
    change pinchCLM (BetaDual.hermLog (diagonal Z)) -
        pinchCLM (BetaDual.hermLog (J+diagonal Z)) - _ =
      pinchCLM (BetaDual.hermLog (diagonal Z) - BetaDual.hermLog (J+diagonal Z)) - _
    rw [map_sub]

theorem hasStrictFDerivAt_jointResidual (lambda : Fin m → ℝ)
    {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n} (hW : W ∈ positiveInterior)
    (hT : (J+diagonal W).mat.PosDef) :
    HasStrictFDerivAt (fun X : HermitianMat (BlockIndex n) ℂ × Blocks n =>
      stationaryResidual X.1 lambda X.2) (jointDerivative J W) (J,W) := by
  let L : (HermitianMat (BlockIndex n) ℂ × Blocks n) →L[ℝ] HermitianMat (BlockIndex n) ℂ :=
    ContinuousLinearMap.fst ℝ _ _+(diagonalCLM (n := n)).comp (ContinuousLinearMap.snd ℝ _ _)
  have ht := (hasStrictFDerivAt_hermLog hT).comp (J,W) L.hasStrictFDerivAt
  have hw := (hasStrictFDerivAt_hermLog (diagonal_posDef hW)).comp (J,W)
    ((diagonalCLM (n := n)).comp (ContinuousLinearMap.snd ℝ _ _)).hasStrictFDerivAt
  have hp := (pinchCLM (n := n)).hasStrictFDerivAt.comp (J,W) (hw.sub ht)
  convert! hp.sub_const (fun i => lambda i • (1 : HermitianMat (Fin (n i)) ℂ)) using 1
  · funext X
    rw [stationaryResidual_eq]
    change pinchCLM (BetaDual.hermLog (diagonal X.2)) -
        pinchCLM (BetaDual.hermLog (X.1+diagonal X.2)) - _ =
      pinchCLM (BetaDual.hermLog (diagonal X.2) - BetaDual.hermLog (X.1+diagonal X.2)) - _
    rw [map_sub]
  · apply ContinuousLinearMap.ext
    intro X
    simp only [jointDerivative,parameterDerivative,residualDerivative,L,
      _root_.add_apply,_root_.sub_apply,_root_.neg_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    rw [map_add,map_sub,map_sub,map_add]
    abel

def blockPairingLM : Blocks n →ₗ[ℝ] (Blocks n →L[ℝ] ℝ) where
  toFun R := ∑ i, (innerSL ℝ (R i)).comp (ContinuousLinearMap.proj i)
  map_add' R S := by
    apply ContinuousLinearMap.ext
    intro H
    simp [Finset.sum_add_distrib]
  map_smul' c R := by
    apply ContinuousLinearMap.ext
    intro H
    simp [Finset.mul_sum]

def blockPairing : Blocks n →L[ℝ] (Blocks n →L[ℝ] ℝ) :=
  (blockPairingLM (n := n)).toContinuousLinearMap

@[simp] theorem blockPairing_apply (R H : Blocks n) :
    blockPairing R H = ∑ i, inner ℝ (R i) (H i) := by
  simp [blockPairing,blockPairingLM]

theorem gradient_eq_blockPairing (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (W : Blocks n) : gradient J lambda W = blockPairing (stationaryResidual J lambda W) := by
  apply ContinuousLinearMap.ext
  intro H
  rw [gradient_apply,blockPairing_apply]
  simp only [real_inner_comm,HermitianMat.inner_eq_re_trace,RCLike.re_eq_complex_re]

theorem hasStrictFDerivAt_gradient {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    {W : Blocks n} (hW : W ∈ positiveInterior) (hT : (J+diagonal W).mat.PosDef) :
    HasStrictFDerivAt (gradient J lambda) ((blockPairing (n := n)).comp (residualDerivative J W)) W := by
  have hp : HasStrictFDerivAt (blockPairing (n := n)) (blockPairing (n := n))
      (stationaryResidual J lambda W) := (blockPairing (n := n)).hasStrictFDerivAt
  have hd : HasStrictFDerivAt
      (fun Z : Blocks n => blockPairing (stationaryResidual J lambda Z))
      ((blockPairing (n := n)).comp (residualDerivative J W)) W := by
    exact HasStrictFDerivAt.comp (f := stationaryResidual J lambda)
      (f' := residualDerivative J W) (g := blockPairing (n := n))
      (g' := blockPairing (n := n)) W hp
      (hasStrictFDerivAt_stationaryResidual lambda hW hT)
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun Z => (gradient_eq_blockPairing J lambda Z).symm)

theorem residualDerivative_pairing {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hW : W ∈ positiveInterior) (hT : (J+diagonal W).mat.PosDef)
    (H K : Blocks n) : blockPairing (residualDerivative J W K) H = hessianRow J W H K := by
  have hd := (hasStrictFDerivAt_gradient (0 : Fin m → ℝ) hW hT).hasFDerivAt.clm_apply
    (hasFDerivAt_const (x := W) H)
  have hr := hasFDerivAt_gradient_row (0 : Fin m → ℝ) hW hT H
  have he := congrArg (fun L : Blocks n →L[ℝ] ℝ => L K) (hd.unique hr)
  simpa using he

theorem residualDerivative_self_pos {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hJ : J.mat.PosDef) (hW : W ∈ positiveInterior) {H : Blocks n} (hne : H ≠ 0) :
    0 < blockPairing (residualDerivative J W H) H := by
  rw [residualDerivative_pairing hW (total_posDef hJ (interior_subset_cone hW))]
  exact hessianRow_self_pos hJ hW hne

theorem residualDerivative_injective {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hJ : J.mat.PosDef) (hW : W ∈ positiveInterior) :
    Function.Injective (residualDerivative J W) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro H hH
  by_contra hne
  have hp := residualDerivative_self_pos hJ hW hne
  rw [hH,map_zero] at hp
  exact (lt_irrefl 0) hp

theorem residualDerivative_isInvertible {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hJ : J.mat.PosDef) (hW : W ∈ positiveInterior) : (residualDerivative J W).IsInvertible := by
  have hi := residualDerivative_injective hJ hW
  let e : Blocks n ≃ₗ[ℝ] Blocks n := LinearEquiv.ofBijective (residualDerivative J W).toLinearMap
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv,rfl⟩

@[simp] theorem jointDerivative_comp_inr (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :
    (jointDerivative J W).comp (ContinuousLinearMap.inr ℝ _ _) = residualDerivative J W := by
  apply ContinuousLinearMap.ext
  intro H
  simp [jointDerivative]

@[simp] theorem jointDerivative_comp_inl (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n) :
    (jointDerivative J W).comp (ContinuousLinearMap.inl ℝ _ _) = parameterDerivative J W := by
  apply ContinuousLinearMap.ext
  intro H
  simp [jointDerivative]

end SchurEntropy.Optimized
