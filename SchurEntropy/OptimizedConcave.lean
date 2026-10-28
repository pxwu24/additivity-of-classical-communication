/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaDualConcave.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.OptimizedHessian
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity
open QubitAdditivity.BetaDualConvex (posDef_convex_combination)

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

/-- Positive-definite input domain of the true minimized dual function. -/
def positiveInputs : Set (HermitianMat (BlockIndex n) ℂ) := {J | J.mat.PosDef}

theorem convex_positiveInputs : Convex ℝ (positiveInputs (n := n)) := by
  intro J hJ K hK a b ha hb hab
  convert! posDef_convex_combination hJ hK ha hb hab using 1

def inputLine (J H : HermitianMat (BlockIndex n) ℂ) (t : ℝ) : HermitianMat (BlockIndex n) ℂ := J+t • H

theorem continuous_inputLine (J H : HermitianMat (BlockIndex n) ℂ) : Continuous (inputLine J H) := by
  unfold inputLine
  fun_prop

theorem hasDerivAt_inputLine (J H : HermitianMat (BlockIndex n) ℂ) (t : ℝ) : HasDerivAt (inputLine J H) H t := by
  convert! ((hasDerivAt_id t).smul_const H).const_add J using 1 <;> simp

theorem inputLine_mem_positiveInputs {J K : HermitianMat (BlockIndex n) ℂ} (hJ : J ∈ positiveInputs)
    (hK : K ∈ positiveInputs) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    inputLine J (K-J) t ∈ positiveInputs := by
  have he : inputLine J (K-J) t = (1-t) • J+t • K := by unfold inputLine; module
  rw [he]
  exact convex_positiveInputs hJ hK (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem hasDerivAt_value_line {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0)
    (J H : HermitianMat (BlockIndex n) ℂ) {t : ℝ} (hJ : (inputLine J H t).mat.PosDef) :
    HasDerivAt (fun u : ℝ => value (inputLine J H u) lambda)
      (valueGradient (inputLine J H t) lambda H) t := by
  convert! (hasFDerivAt_value hJ hl).comp_hasDerivAt t (hasDerivAt_inputLine J H t) using 1

/-- The true scalar second derivative uses the already identified Schur Hessian. -/
theorem hasDerivAt_deriv_value_line {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0)
    (J H : HermitianMat (BlockIndex n) ℂ) {t : ℝ} (hJ : (inputLine J H t).mat.PosDef) :
    HasDerivAt (deriv (fun u : ℝ => value (inputLine J H u) lambda))
      (valueHessianRow (inputLine J H t) lambda H H) t := by
  have hd : HasDerivAt (fun u : ℝ => valueGradient (inputLine J H u) lambda H)
      (valueHessianRow (inputLine J H t) lambda H H) t := by
    convert! (hasFDerivAt_valueGradient_row hJ hl H).comp_hasDerivAt t
      (hasDerivAt_inputLine J H t) using 1
  have hp : ∀ᶠ u : ℝ in 𝓝 t, (inputLine J H u).mat.PosDef :=
    (continuous_inputLine J H).tendsto t |>.eventually (BetaLog.eventually_posDef hJ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hp] with u hu
  exact (hasDerivAt_value_line hl J H hu).deriv

theorem concaveOn_value_line {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0)
    {J K : HermitianMat (BlockIndex n) ℂ} (hJ : J ∈ positiveInputs) (hK : K ∈ positiveInputs) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t : ℝ => value (inputLine J (K-J) t) lambda) := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := inputLine_mem_positiveInputs hJ hK ht
  apply concaveOn_of_deriv2_nonpos' (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_value_line hl J (K-J) (hp t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_deriv_value_line hl J (K-J) (hp t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    change deriv (deriv (fun u : ℝ => value (inputLine J (K-J) u) lambda)) t ≤ 0
    rw [(hasDerivAt_deriv_value_line hl J (K-J) (hp t ht)).deriv]
    exact valueHessianRow_self_nonpos (hp t ht) hl (K-J)

/-- Actual concavity of the manuscript's minimized dual value on all J>0. -/
theorem concaveOn_value {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0) :
    ConcaveOn ℝ positiveInputs (fun J : HermitianMat (BlockIndex n) ℂ => value J lambda) := by
  refine ⟨convex_positiveInputs,?_⟩
  intro J hJ K hK a b ha hb hab
  have hs := concaveOn_value_line hl hJ hK
  have hi := hs.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ha hb hab
  have he : inputLine J (K-J) (a • (0 : ℝ)+b • (1 : ℝ)) = a • J+b • K := by
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add,inputLine]
    have hh : 1-b = a := by linarith
    calc
      J+b • (K-J) = (1-b) • J+b • K := by module
      _ = _ := by rw [hh]
  have h₀ : inputLine J (K-J) 0 = J := by simp [inputLine]
  have h₁ : inputLine J (K-J) 1 = K := by simp [inputLine]
  simpa only [he,h₀,h₁] using hi

end SchurEntropy.Optimized
