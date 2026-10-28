/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaDualBoundary.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.OptimizedExistence

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaEntropy
open QubitAdditivity.BetaDualExistence (continuous_psi norm_le_trace tendsto_scalar_lower_bound)
open QubitAdditivity.BetaDual (traceHerm)

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



variable {k : Type*} [Fintype k] [DecidableEq k]
variable {m : ℕ} {n : Fin m → ℕ}

theorem eq_zero_of_trace_zero {J : HermitianMat k ℂ} (hJ : J.mat.PosSemidef)
    (hz : J.mat.trace.re = 0) : J = 0 := by
  exact norm_eq_zero.mp (le_antisymm (by simpa [hz] using norm_le_trace hJ) (norm_nonneg J))

/-- The positive-input coercivity estimate extends to every PSD input by continuity. -/
theorem objective_lower_bound_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ} {c : ℝ}
    (hJ : J.mat.PosSemidef) (hc : ∀ i, c ≤ -lambda i)
    {W : Blocks n} (hW : W ∈ positiveCone) :
    c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      objective J lambda W := by
  have hm : 0 ≤ J.mat.trace.re := le_trans (norm_nonneg J) (norm_le_trace hJ)
  by_cases hz : J.mat.trace.re = 0
  · have he := eq_zero_of_trace_zero hJ hz
    subst J
    have hlp := penalty_lower_bound hc hW
    unfold objective
    simp only [zero_add,HermitianMat.mat_zero,Matrix.trace_zero,Complex.zero_re,zero_mul,sub_zero]
    linarith
  have hp : 0 < J.mat.trace.re := lt_of_le_of_ne hm (Ne.symm hz)
  let f : ℝ → HermitianMat (BlockIndex n) ℂ := fun t => J+t • 1
  have hf : Continuous f := by unfold f; fun_prop
  have htr : Continuous (fun t => (f t).mat.trace.re) := by
    convert! (traceHerm (k := BlockIndex n)).continuous.comp hf using 1
  have hlog : ContinuousAt (fun t => Real.log (blockTrace W+(f t).mat.trace.re)) 0 := by
    have hq : 0 ≤ blockTrace W := blockTrace_nonneg hW
    have hqp : 0 < blockTrace W+J.mat.trace.re := by linarith
    have hn : blockTrace W+(f 0).mat.trace.re ≠ 0 := by simpa [f] using hqp.ne'
    exact (Real.continuousAt_log hn).comp (x := 0)
      (show ContinuousAt (fun t : ℝ => blockTrace W+(f t).mat.trace.re) 0 from
        (continuous_const.add htr).continuousAt)
  have hl : Tendsto (fun t => c*blockTrace W-(f t).mat.trace.re*(Real.log (blockTrace W+(f t).mat.trace.re)+1))
      (𝓝[>] 0) (𝓝 (c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1))) := by
    have hh : ContinuousAt (fun t : ℝ => c*blockTrace W-
        (f t).mat.trace.re*(Real.log (blockTrace W+(f t).mat.trace.re)+1)) 0 :=
      continuousAt_const.sub (htr.continuousAt.mul (hlog.add continuousAt_const))
    simpa [f] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have ho : Continuous (fun t => objective (f t) lambda W) := by
    unfold objective
    exact continuous_const.sub (continuous_psi.comp (hf.add continuous_const)) |>.sub continuous_const
  have hr : Tendsto (fun t => objective (f t) lambda W) (𝓝[>] 0)
      (𝓝 (objective J lambda W)) := by
    have he : f (0 : ℝ) = J := by simp [f]
    have ht : Tendsto (fun t : ℝ => objective (f t) lambda W) (𝓝[>] 0)
        (𝓝 (objective (f 0) lambda W)) := (ho.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    rw [he] at ht
    exact ht
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hj : (f t).mat.PosDef := by
    change (J.mat+t • (1 : Matrix (BlockIndex n) (BlockIndex n) ℂ)).PosDef
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) ht').add_posSemidef hJ
  exact objective_lower_bound hj hc hW

/-- One common lower bound for every bounded family of PSD inputs, including J=0. -/
theorem objective_uniform_lower_bound {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ} {c M : ℝ}
    (hJ : J.mat.PosSemidef) (hc : ∀ i, c ≤ -lambda i)
    (hM : 1 ≤ M) (hmM : J.mat.trace.re ≤ M) {W : Blocks n} (hW : W ∈ positiveCone) :
    c*blockTrace W-M*(Real.log (blockTrace W+M)+1) ≤ objective J lambda W := by
  have hm : 0 ≤ J.mat.trace.re := le_trans (norm_nonneg J) (norm_le_trace hJ)
  have hq := blockTrace_nonneg hW
  have hL : 0 ≤ Real.log (blockTrace W+M)+1 := by
    have hh : 1 ≤ blockTrace W+M := by linarith
    linarith [Real.log_nonneg hh]
  have hi : J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      M*(Real.log (blockTrace W+M)+1) := by
    by_cases hz : J.mat.trace.re = 0
    · simpa [hz] using mul_nonneg (by linarith : 0 ≤ M) hL
    have hp : 0 < blockTrace W+J.mat.trace.re := by
      exact add_pos_of_nonneg_of_pos hq (lt_of_le_of_ne hm (Ne.symm hz))
    have hl := Real.log_le_log hp (show blockTrace W+J.mat.trace.re ≤ blockTrace W+M by linarith)
    exact (mul_le_mul_of_nonneg_left (add_le_add hl le_rfl) hm).trans
      (mul_le_mul_of_nonneg_right hmM hL)
  exact (sub_le_sub_left hi _).trans (objective_lower_bound_psd hJ hc hW)

/-- Uniform coercivity on any trace-bounded PSD input family. -/
theorem exists_uniform_trace_threshold {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0)
    {M : ℝ} (hM : 1 ≤ M) (a : ℝ) : ∃ R : ℝ, ∀ (J : HermitianMat (BlockIndex n) ℂ) (W : Blocks n),
      J.mat.PosSemidef → J.mat.trace.re ≤ M → W ∈ positiveCone → R ≤ blockTrace W →
        a ≤ objective J lambda W := by
  obtain ⟨c, hcp, hcl⟩ := exists_uniform_positive hl
  obtain ⟨R,hR⟩ := eventually_atTop.1 ((tendsto_scalar_lower_bound c M hcp).eventually_ge_atTop a)
  refine ⟨R,?_⟩
  intro J W hJ hmM hW hlarge
  exact (hR (blockTrace W) hlarge).trans
    (objective_uniform_lower_bound hJ hcl hM hmM hW)

theorem objective_eventually_ge_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) (a : ℝ) :
    ∀ᶠ W in cocompact (Blocks n) ⊓ 𝓟 positiveCone, a ≤ objective J lambda W := by
  obtain ⟨R,hR⟩ := exists_uniform_trace_threshold (n := n) hl
    (M := max 1 J.mat.trace.re) (le_max_left _ _) a
  rw [eventually_inf_principal]
  filter_upwards [(isCompact_traceSublevel (n := n) R).compl_mem_cocompact]
    with W houtside hW
  have hlarge : R ≤ blockTrace W := by
    by_contra! hsmall
    exact houtside ⟨hW,hsmall.le⟩
  exact hR J W hJ (le_max_right _ _) hW hlarge

/-- Actual minima exist even for singular PSD inputs; no uniqueness or interiority is imposed. -/
theorem exists_minOn_positiveCone_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) :
    ∃ W ∈ positiveCone, IsMinOn (objective J lambda) positiveCone W := by
  apply (continuous_objective J lambda).continuousOn.exists_isMinOn' isClosed_positiveCone
    (x₀ := (0 : Blocks n))
  · intro i; exact Matrix.PosSemidef.zero
  · exact objective_eventually_ge_psd hJ hl _

end SchurEntropy.Optimized
