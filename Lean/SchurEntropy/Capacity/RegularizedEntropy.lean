import SchurEntropy.LogOrder
import QubitAdditivity.BetaDualExistence

/-! A regularized logarithmic upper bound on a spectral-entropy increment.
The bound applies at singular positive matrices and uses a fixed spectral basis
for the regularizing logarithm. -/

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Capacity
open QubitAdditivity QubitAdditivity.BetaEntropy QubitAdditivity.BetaPowers

variable {k : Type*} [Fintype k] [DecidableEq k]

@[reducible] local instance mNorm : NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace : NormedSpace ℝ (Matrix k k ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] local instance mTop : TopologicalSpace (Matrix k k ℂ) :=
  mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd : AddCommGroup (Matrix k k ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule : Module ℝ (Matrix k k ℂ) := mSpace.toModule
@[reducible] local instance hTop : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule

/-- Positive test matrices preserve the Loewner comparison of two logarithms. -/
theorem trace_log_mono {A B R : HermitianMat k ℂ} (hA : A.mat.PosDef)
    (hAB : (B-A).mat.PosSemidef) (hR : R.mat.PosSemidef) :
    (R.mat * logarithm A.mat).trace.re ≤ (R.mat * logarithm B.mat).trace.re := by
  have hl : (logarithm B.mat - logarithm A.mat).PosSemidef :=
    logarithm_sub_posSemidef hA hAB
  let L : HermitianMat k ℂ := ⟨_, hl.isHermitian⟩
  have hL : 0 ≤ L := HermitianMat.zero_le_iff.mpr hl
  have hr : 0 ≤ R := HermitianMat.zero_le_iff.mpr hR
  have hi := HermitianMat.inner_ge_zero hr hL
  rw [HermitianMat.inner_eq_re_trace] at hi
  change 0 ≤ (R.mat * (logarithm B.mat - logarithm A.mat)).trace.re at hi
  simpa [Matrix.mul_sub] using hi

/-- A bounded positive direction can be estimated with the scalar identity
regularization of the base, even when the base is singular. -/
theorem psi_increment_le_regularized_log {A R : HermitianMat k ℂ}
    (hA : A.mat.PosSemidef) (hR : R.mat.PosSemidef) (hR1 : R ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    psi (A+t • R)-psi A ≤
      t*((R.mat * logarithm (A+t • 1).mat).trace.re+R.mat.trace.re) := by
  let W : ℝ → HermitianMat k ℂ := fun ε => A+ε • 1
  let Y : ℝ → HermitianMat k ℂ := fun ε => A+(ε+t) • 1
  have hW (ε : ℝ) (hε : 0 < ε) : (W ε).mat.PosDef := by
    change (A.mat+ε • (1 : Matrix k k ℂ)).PosDef
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) hε).add_posSemidef hA
  have hbound (ε : ℝ) (hε : 0 < ε) :
      psi (W ε+t • R)-psi (W ε) ≤
        t*((R.mat * logarithm (Y ε).mat).trace.re+R.mat.trace.re) := by
    have hT : (W ε+t • R).mat.PosDef := (hW ε hε).add_posSemidef (hR.smul ht.le)
    have hi := BetaDualExistence.psi_increment_le_gradient
      (W := W ε) (J := t • R) (hW ε hε).posSemidef (hR.smul ht.le) hT
    have hdiff : (Y ε-(W ε+t • R)).mat.PosSemidef := by
      have he : Y ε-(W ε+t • R) = t • (1-R) := by dsimp [Y,W]; module
      rw [he]
      exact (HermitianMat.zero_le_iff.mp (sub_nonneg.mpr hR1)).smul ht.le
    have hl := trace_log_mono hT hdiff hR
    have hm := mul_le_mul_of_nonneg_left hl ht.le
    rw [psiGradient_apply] at hi
    have he : ((t • R).mat * (logarithm (W ε+t • R).mat+1)).trace.re =
        t*((R.mat*logarithm (W ε+t • R).mat).trace.re+R.mat.trace.re) := by
      simp [mul_add]
    rw [he] at hi
    linarith
  have hcW : Continuous W := by dsimp [W]; fun_prop
  have hcY : Continuous Y := by dsimp [Y]; fun_prop
  have hleft : Tendsto (fun ε => psi (W ε+t • R)-psi (W ε)) (𝓝[>] 0)
      (𝓝 (psi (A+t • R)-psi A)) := by
    have hc : Continuous (fun ε => psi (W ε+t • R)-psi (W ε)) :=
      (BetaDualExistence.continuous_psi.comp (hcW.add continuous_const)).sub
      (BetaDualExistence.continuous_psi.comp hcW)
    simpa [W] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hy : (Y 0).mat.PosDef := by
    change (A.mat+(0+t) • (1 : Matrix k k ℂ)).PosDef
    simp only [zero_add]
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) ht).add_posSemidef hA
  have hlog : ContinuousAt (fun ε => logarithm (Y ε).mat) 0 :=
    (BetaLog.hasFDerivAt_logarithm hy).continuousAt.comp hcY.continuousAt
  let L : Matrix k k ℂ →L[ℝ] ℝ := (BetaLog.traceRe (n := k)).comp
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix k k ℂ) R.mat 1)
  have hpair : ContinuousAt (fun ε => (R.mat * logarithm (Y ε).mat).trace.re) 0 := by
    convert! L.continuous.continuousAt.comp hlog using 1
    ext ε
    simp [L, BetaLog.traceRe_apply]
  have hright : Tendsto (fun ε => t*((R.mat * logarithm (Y ε).mat).trace.re+R.mat.trace.re))
      (𝓝[>] 0) (𝓝 (t*((R.mat * logarithm (A+t • 1).mat).trace.re+R.mat.trace.re))) := by
    have hc : ContinuousAt (fun ε => t*((R.mat * logarithm (Y ε).mat).trace.re+R.mat.trace.re)) 0 :=
      (hpair.add continuousAt_const).const_mul t
    simpa [Y] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

end SchurEntropy.Capacity
