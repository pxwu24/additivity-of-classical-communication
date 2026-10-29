import SchurEntropy.LogOrder
import QubitAdditivity.BetaEntropy
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Monotonicity of an entropy increment

This file uses the matrix entropy derivative from the pinned
`qubitStrongAdditivity` dependency. Entropy is unnormalized throughout.
-/

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy
namespace EntropyIncrement
open QubitAdditivity QubitAdditivity.BetaEntropy

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

local instance matrixCFC : ContinuousFunctionalCalculus ℝ (Matrix k k ℂ) Matrix.IsHermitian := by
  let : TopologicalSpace (Matrix k k ℂ) := inferInstanceAs (TopologicalSpace (k → k → ℂ))
  let : AddCommGroup (Matrix k k ℂ) := Matrix.addCommGroup
  let : Module ℝ (Matrix k k ℂ) := Matrix.module
  convert! (Matrix.IsHermitian.instContinuousFunctionalCalculus (𝕜 := ℂ) (n := k)) using 1

theorem gradient_increment_nonneg {W J D : HermitianMat k ℂ}
    (hW : W.mat.PosDef) (hJ : J.mat.PosSemidef) (hD : D.mat.PosSemidef) :
    0 ≤ psiGradient (W + J).mat D - psiGradient W.mat D := by
  have hlog : (cfc Real.log (W + J).mat - cfc Real.log W.mat).PosSemidef :=
    logarithm_sub_posSemidef (B := (W + J).mat) hW (by simpa using hJ)
  let L : HermitianMat k ℂ := ⟨_, hlog.isHermitian⟩
  have hD0 : 0 ≤ D := HermitianMat.zero_le_iff.mpr hD
  have hL0 : 0 ≤ L := HermitianMat.zero_le_iff.mpr hlog
  have hi := HermitianMat.inner_ge_zero hD0 hL0
  rw [HermitianMat.inner_eq_re_trace] at hi
  change 0 ≤ (D.mat * (cfc Real.log (W + J).mat - cfc Real.log W.mat)).trace.re at hi
  simp only [psiGradient_apply, BetaPowers.logarithm, Matrix.mul_sub,
    Matrix.mul_add, Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re] at hi ⊢
  convert! hi using 1
  ring_nf
  rfl

/-- For a strictly positive base, the negative entropy increment increases
under a positive semidefinite change of the base. -/
theorem psi_increment_mono_posDef {W J D : HermitianMat k ℂ}
    (hW : W.mat.PosDef) (hJ : J.mat.PosSemidef) (hD : D.mat.PosSemidef) :
    psi (W + J) - psi W ≤ psi (W + D + J) - psi (W + D) := by
  let f : ℝ → ℝ := fun t => psi (W + t • D + J) - psi (W + t • D)
  let f' : ℝ → ℝ := fun t =>
    psiGradient (W + t • D + J).mat D - psiGradient (W + t • D).mat D
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (W + t • D).mat.PosDef :=
    hW.add_posSemidef (hD.smul ht.1)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t := by
    have hpath : HasDerivAt (fun s : ℝ => W + s • D) D t := by
      simpa using ((hasDerivAt_id t).smul_const D).const_add W
    have hpj : (W + t • D + J).mat.PosDef := (hp t ht).add_posSemidef hJ
    exact ((hasFDerivAt_psi hpj).comp_hasDerivAt t
      (hpath.add_const J)).sub ((hasFDerivAt_psi (hp t ht)).comp_hasDerivAt t hpath)
  have hm : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => gradient_increment_nonneg (hp t (interior_subset ht)) hJ hD)
  simpa [f] using hm (by simp) (by simp) zero_le_one

/-- The zero-eigenvalue convention makes negative entropy continuous. -/
theorem continuous_psi : Continuous (psi : HermitianMat k ℂ → ℝ) := by
  have hc := (BetaLog.traceRe (n := k)).continuous.comp
    ((BetaLog.inclusion (n := k)).continuous.comp
      (HermitianMat.cfc_continuous Real.continuous_negMulLog))
  convert! hc.neg using 1

/-- The monotonicity statement includes singular bases, by a positive
identity perturbation and continuity at zero eigenvalues. -/
theorem psi_increment_mono {W J D : HermitianMat k ℂ}
    (hW : W.mat.PosSemidef) (hJ : J.mat.PosSemidef) (hD : D.mat.PosSemidef) :
    psi (W + J) - psi W ≤ psi (W + D + J) - psi (W + D) := by
  let f : ℝ → HermitianMat k ℂ := fun t => W + t • 1
  have hf : Continuous f := by unfold f; fun_prop
  have hl : Continuous (fun t => psi (f t + J) - psi (f t)) :=
    (continuous_psi.comp (hf.add continuous_const)).sub (continuous_psi.comp hf)
  have hr : Continuous (fun t => psi (f t + D + J) - psi (f t + D)) :=
    (continuous_psi.comp ((hf.add continuous_const).add continuous_const)).sub
      (continuous_psi.comp (hf.add continuous_const))
  have hleft : Tendsto (fun t => psi (f t + J) - psi (f t)) (𝓝[>] 0)
      (𝓝 (psi (W + J) - psi W)) := by
    simpa [f] using (hl.tendsto 0).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t => psi (f t + D + J) - psi (f t + D)) (𝓝[>] 0)
      (𝓝 (psi (W + D + J) - psi (W + D))) := by
    simpa [f] using (hr.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp : (f t).mat.PosDef := by
    change (W.mat + t • (1 : Matrix k k ℂ)).PosDef
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) ht).add_posSemidef hW
  exact psi_increment_mono_posDef hp hJ hD

end EntropyIncrement

/-- The entropy increment is antitone in its positive semidefinite base.
This is the logarithm-monotonicity step in the rank-one argument. -/
theorem entropy_increment_antitone {k : Type*} [Fintype k] [DecidableEq k]
    {J W Y : Matrix k k ℂ} (hJ : J.PosSemidef) (hW : W.PosSemidef)
    (hWY : (Y - W).PosSemidef) :
    entropy (J + Y) - entropy Y ≤ entropy (J + W) - entropy W := by
  let j : HermitianMat k ℂ := ⟨J, hJ.isHermitian⟩
  let w : HermitianMat k ℂ := ⟨W, hW.isHermitian⟩
  let d : HermitianMat k ℂ := ⟨Y - W, hWY.isHermitian⟩
  have hi := EntropyIncrement.psi_increment_mono (W := w) (J := j) (D := d) hW hJ hWY
  have he : (w + d).mat = Y := by change W + (Y - W) = Y; abel
  simp only [QubitAdditivity.BetaEntropy.psi, HermitianMat.mat_add, he] at hi
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold entropy
  rw [← sub_div, ← sub_div]
  apply (div_le_div_iff_of_pos_right hlog).mpr
  change (QubitAdditivity.OpenAIEntropy.entropy (J + Y) -
    QubitAdditivity.OpenAIEntropy.entropy Y) ≤
    QubitAdditivity.OpenAIEntropy.entropy (J + W) -
    QubitAdditivity.OpenAIEntropy.entropy W
  change -QubitAdditivity.OpenAIEntropy.entropy (W + J) -
    -QubitAdditivity.OpenAIEntropy.entropy W ≤
    -QubitAdditivity.OpenAIEntropy.entropy (Y + J) -
    -QubitAdditivity.OpenAIEntropy.entropy Y at hi
  rw [add_comm W J, add_comm Y J] at hi
  linarith

end SchurEntropy
