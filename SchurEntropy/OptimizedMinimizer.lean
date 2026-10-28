/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaMinimizer.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.OptimizedDerivative

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity

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

/-- A positive stationary point minimizes the actual objective on the positive interior. -/
theorem isMinOn_interior_of_stationary {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) {W : Blocks n} (hW : W ∈ positiveInterior)
    (hs : stationaryResidual J lambda W = 0) :
    IsMinOn (objective J lambda) positiveInterior W := by
  intro Z hZ
  by_cases he : W = Z
  · subst Z
    exact le_refl (objective J lambda W)
  have hc := (strictConvexOn_objective_line lambda hJ hW hZ he).convexOn
  have hd := hasDerivAt_objective_line lambda W (Z-W)
    (t := 0) (by simpa [line] using hW)
    (by simpa [line] using total_posDef hJ (interior_subset_cone hW))
  have hz : gradient J lambda (line W (Z-W) 0) (Z-W) = 0 := by
    simp only [line,zero_smul,add_zero,gradient_eq_blockPairing,hs,map_zero]
    rfl
  rw [hz] at hd
  have hi := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hd
  simpa [slope_def_field,line,sub_le_iff_le_add] using hi

theorem eq_of_stationary {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) {W Z : Blocks n} (hW : W ∈ positiveInterior) (hZ : Z ∈ positiveInterior)
    (hsW : stationaryResidual J lambda W = 0)
    (hsZ : stationaryResidual J lambda Z = 0) : W = Z :=
  (strictConvexOn_objective lambda hJ).eq_of_isMinOn
    (isMinOn_interior_of_stationary hJ hW hsW) (isMinOn_interior_of_stationary hJ hZ hsZ) hW hZ

/-- A total choice of the true cone minimum, used only where existence is established. -/
def minimizer (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) : Blocks n :=
  Classical.epsilon (fun W => W ∈ positiveCone ∧ IsMinOn (objective J lambda) positiveCone W)

theorem minimizer_spec {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    minimizer J lambda ∈ positiveCone ∧
      IsMinOn (objective J lambda) positiveCone (minimizer J lambda) := by
  obtain ⟨W,hW,hmin⟩ := exists_minOn_positiveCone hJ hl
  exact Classical.epsilon_spec (p := fun W : Blocks n =>
    W ∈ positiveCone ∧ IsMinOn (objective J lambda) positiveCone W) ⟨W,hW,hmin⟩

theorem minimizer_positiveInterior {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    minimizer J lambda ∈ positiveInterior := by
  have hs := minimizer_spec hJ hl
  exact positiveInterior_of_minOn hJ hs.1 hs.2

theorem minimizer_stationary {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    stationaryResidual J lambda (minimizer J lambda) = 0 := by
  have hs := minimizer_spec hJ hl
  exact stationarity_of_minOn hJ hs.1 hs.2

def minimizerDerivative (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) :
    HermitianMat (BlockIndex n) ℂ →L[ℝ] Blocks n :=
  (-(residualDerivative J (minimizer J lambda)).inverse).comp
    (parameterDerivative J (minimizer J lambda))

/-- The true global cone minimizer is strictly Fréchet differentiable on J>0. -/
theorem hasStrictFDerivAt_minimizer {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    HasStrictFDerivAt (fun K : HermitianMat (BlockIndex n) ℂ => minimizer K lambda)
      (minimizerDerivative J lambda) J := by
  let W := minimizer J lambda
  have hW := minimizer_positiveInterior hJ hl
  have hT := total_posDef hJ (interior_subset_cone hW)
  let df := hasStrictFDerivAt_jointResidual lambda hW hT
  have hi : ((jointDerivative J W).comp (ContinuousLinearMap.inr ℝ _ _)).IsInvertible := by
    rw [jointDerivative_comp_inr]
    exact residualDerivative_isInvertible hJ hW
  let f := df.implicitFunctionOfProdDomain hi
  have hd : HasStrictFDerivAt f (minimizerDerivative J lambda) J := by
    convert! df.hasStrictFDerivAt_implicitFunctionOfProdDomain hi using 1 <;>
      simp only [jointDerivative_comp_inr,jointDerivative_comp_inl,minimizerDerivative,ContinuousLinearMap.neg_comp]
  have hc : Tendsto f (𝓝 J) (𝓝 W) := df.tendsto_implicitFunctionOfProdDomain hi
  have hp : ∀ᶠ K in 𝓝 J, f K ∈ positiveInterior :=
    hc.eventually (positiveInterior_mem_nhds hW)
  have hs : ∀ᶠ K in 𝓝 J, stationaryResidual K lambda (f K) = 0 := by
    filter_upwards [df.eventually_apply_implicitFunctionOfProdDomain hi] with K hK
    exact hK.trans (minimizer_stationary hJ hl)
  apply hd.congr_of_eventuallyEq
  filter_upwards [BetaLog.eventually_posDef hJ,hp,hs] with K hK hpos hstat
  exact eq_of_stationary hK hpos (minimizer_positiveInterior hK hl)
    hstat (minimizer_stationary hK hl)

theorem continuousAt_minimizer {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    ContinuousAt (fun K : HermitianMat (BlockIndex n) ℂ => minimizer K lambda) J :=
  (hasStrictFDerivAt_minimizer hJ hl).continuousAt

end SchurEntropy.Optimized
