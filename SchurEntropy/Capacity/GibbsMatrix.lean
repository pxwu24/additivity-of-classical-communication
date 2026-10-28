/-
The scalar-line tangent argument adapts the convexity/derivative pattern in
KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/BetaDualExistence.lean (Apache-2.0).
It is restated for an arbitrary PSD endpoint and a PD tangent point, with
Klein's unnormalized trace correction. See third_party/NOTICE.
-/
import QubitAdditivity.BetaDualExistence
import Mathlib.Analysis.Convex.Deriv

/-!
# Gibbs' entropy bound, including singular output centers

The regularized bound follows from the proved convexity and derivative of
`Tr X log X`. It uses unnormalized positive matrices, so the trace correction
is retained explicitly before taking the regularization limit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Capacity
namespace Gibbs
open QubitAdditivity QubitAdditivity.BetaEntropy

variable {d : Type*} [Fintype d] [DecidableEq d]

@[reducible] private local instance mNorm : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] private local instance mSpace : NormedSpace ℝ (Matrix d d ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix d d ℂ)
@[reducible] private local instance mTop : TopologicalSpace (Matrix d d ℂ) :=
  mNorm.toUniformSpace.toTopologicalSpace
@[reducible] private local instance mAdd : AddCommGroup (Matrix d d ℂ) := mNorm.toAddCommGroup
@[reducible] private local instance mModule : Module ℝ (Matrix d d ℂ) := mSpace.toModule
@[reducible] private local instance hTop : TopologicalSpace (HermitianMat d ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] private local instance hAdd : AddCommGroup (HermitianMat d ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] private local instance hModule : Module ℝ (HermitianMat d ℂ) :=
  HermitianMat.instNormedSpace.toModule

/-- The entropy tangent at a positive definite matrix bounds every PSD input. -/
theorem psi_tangent_le {X Y : HermitianMat d ℂ}
    (hX : X.mat.PosSemidef) (hY : Y.mat.PosDef) :
    psi Y + psiGradient Y.mat (X - Y) ≤ psi X := by
  let f : ℝ → ℝ := fun t => psi (Y + t • (X - Y))
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (Y + t • (X - Y)).mat.PosSemidef := by
    have he : Y + t • (X - Y) = (1 - t) • Y + t • X := by module
    rw [he]
    exact (hY.posSemidef.smul (sub_nonneg.mpr ht.2)).add (hX.smul ht.1)
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) f := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have he : Y + (a * x + b * y) • (X - Y) =
        a • (Y + x • (X - Y)) + b • (Y + y • (X - Y)) := by
      have hy0 : (a + b) • Y = Y := by rw [hab, one_smul]
      calc
        _ = (a + b) • Y + (a * x + b * y) • (X - Y) := by rw [hy0]
        _ = _ := by module
    change psi (Y + (a * x + b * y) • (X - Y)) ≤
      a * psi (Y + x • (X - Y)) + b * psi (Y + y • (X - Y))
    rw [he]
    exact BetaDualExistence.convex_psi.2 (hp x hx) (hp y hy) ha hb hab
  have hd : HasDerivAt f (psiGradient Y.mat (X - Y)) 0 := by
    have hl : HasDerivAt (fun t : ℝ => Y + t • (X - Y)) (X - Y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (X - Y)).const_add Y
    have hy : (Y + (0 : ℝ) • (X - Y)).mat.PosDef := by simpa using hY
    convert! (hasFDerivAt_psi hy).comp_hasDerivAt 0 hl using 1 <;> simp
  have hi := hc.le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) (by norm_num) hd
  simp only [slope_def_field, f, one_smul, zero_smul, add_zero, sub_zero, div_one] at hi
  have he : Y + (X - Y) = X := by abel
  rw [he] at hi
  linarith

/-- Klein's inequality in the form needed here, with the exact trace
correction for unnormalized matrices. -/
theorem entropy_log_le_trace_sub {X Y : HermitianMat d ℂ}
    (hX : X.mat.PosSemidef) (hY : Y.mat.PosDef) :
    OpenAIEntropy.entropy X.mat + (X.mat * BetaPowers.logarithm Y.mat).trace.re ≤
      Y.mat.trace.re - X.mat.trace.re := by
  have ht := psi_tangent_le hX hY
  rw [psi_eq_trace Y, psiGradient_apply] at ht
  simp only [HermitianMat.mat_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re] at ht
  change _ ≤ -OpenAIEntropy.entropy X.mat at ht
  linarith

end Gibbs
end SchurEntropy.Capacity
