/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaDualBoundary.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.OptimizedConcave
import SchurEntropy.OptimizedPSDExistence

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

theorem minimizer_spec_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) :
    minimizer J lambda ∈ positiveCone ∧
      IsMinOn (objective J lambda) positiveCone (minimizer J lambda) := by
  obtain ⟨W,hW,hmin⟩ := exists_minOn_positiveCone_psd hJ hl
  exact Classical.epsilon_spec (p := fun W : Blocks n =>
    W ∈ positiveCone ∧ IsMinOn (objective J lambda) positiveCone W) ⟨W,hW,hmin⟩

/-- Joint entropy continuity on the full real parameter space, including singular points. -/
theorem continuous_jointObjective (lambda : Fin m → ℝ) :
    Continuous (fun X : HermitianMat (BlockIndex n) ℂ × Blocks n => objective X.1 lambda X.2) := by
  have hd : Continuous (fun X : HermitianMat (BlockIndex n) ℂ × Blocks n => diagonal X.2) :=
    (diagonalCLM (n := n)).continuous.comp continuous_snd
  have hc : Continuous (fun X : HermitianMat (BlockIndex n) ℂ × Blocks n =>
      psi (diagonal X.2)-psi (X.1+diagonal X.2)-linearPenalty lambda X.2) :=
    ((continuous_psi.comp hd).sub (continuous_psi.comp (continuous_fst.add hd))).sub
      ((linearPenalty (n := n) lambda).continuous.comp continuous_snd)
  exact hc

/-- Every local trace-bounded family has all of its true minima in one compact set. -/
theorem continuousWithinAt_minimumValue_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) :
    ContinuousWithinAt (fun K : HermitianMat (BlockIndex n) ℂ => minimumValue K lambda)
      {K | K.mat.PosSemidef} J := by
  let M := max 1 J.mat.trace.re+1
  let a := -psi J+1
  have hM : 1 ≤ M := (le_max_left (1 : ℝ) J.mat.trace.re).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨R,hR⟩ := exists_uniform_trace_threshold (n := n) hl hM a
  let C : Set (Blocks n) := {W | W ∈ positiveCone ∧ blockTrace W ≤ R}
  have hm : ∀ᶠ K : HermitianMat (BlockIndex n) ℂ in 𝓝 J, K.mat.trace.re ≤ M := by
    have hc : Continuous (fun K : HermitianMat (BlockIndex n) ℂ => K.mat.trace.re) := by
      convert! (traceHerm (k := BlockIndex n)).continuous using 1
    have hJM : J.mat.trace.re < M := (le_max_right (1 : ℝ) J.mat.trace.re).trans_lt (lt_add_one _)
    have hlt : ∀ᶠ K : HermitianMat (BlockIndex n) ℂ in 𝓝 J, K.mat.trace.re < M :=
      (hc.continuousAt (x := J)).eventually_lt (continuousAt_const (x := J) (y := M)) hJM
    exact hlt.mono fun K hK => hK.le
  have ha : ∀ᶠ K : HermitianMat (BlockIndex n) ℂ in 𝓝 J, objective K lambda (0 : Blocks n) < a := by
    have hbase (K : HermitianMat (BlockIndex n) ℂ) : objective K lambda (0 : Blocks n) = -psi K := by
      unfold objective
      rw [diagonal_zero,add_zero,map_zero]
      have hz : psi (0 : HermitianMat (BlockIndex n) ℂ) = 0 := by
        rw [psi_eq_trace]
        simp
      simp [hz]
    have hh : ∀ᶠ K : HermitianMat (BlockIndex n) ℂ in 𝓝 J, -psi K < a :=
      ((continuous_psi (k := BlockIndex n)).neg.continuousAt (x := J)).eventually_lt
        (continuousAt_const (x := J) (y := a)) (lt_add_one _)
    exact hh.mono fun K hK => by rw [hbase K]; exact hK
  have he : ∀ᶠ K : HermitianMat (BlockIndex n) ℂ in 𝓝[{K | K.mat.PosSemidef}] J,
      minimumValue K lambda = sInf (objective K lambda '' C) := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds,ha.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with K hmK haK hK
    have hs := minimizer_spec_psd hK hl
    have hzero : (0 : Blocks n) ∈ positiveCone := fun i => Matrix.PosSemidef.zero
    have hmin : objective K lambda (minimizer K lambda) ≤ objective K lambda 0 := hs.2 hzero
    have hq : blockTrace (minimizer K lambda) < R := by
      by_contra! hn
      have hi := hR K (minimizer K lambda) hK hmK hs.1 hn
      exact (not_lt_of_ge (hi.trans hmin)) haK
    have his : IsLeast (objective K lambda '' C) (minimumValue K lambda) := by
      refine ⟨⟨minimizer K lambda,⟨hs.1,hq.le⟩,rfl⟩,?_⟩
      rintro _ ⟨Z,hZ,rfl⟩
      exact hs.2 hZ.1
    exact his.csInf_eq.symm
  have hc : Continuous (fun K : HermitianMat (BlockIndex n) ℂ => sInf (objective K lambda '' C)) :=
    (isCompact_traceSublevel R).continuous_sInf (continuous_jointObjective lambda)
  exact hc.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem he hJ

theorem continuousOn_minimumValue_psd {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0) :
    ContinuousOn (fun J : HermitianMat (BlockIndex n) ℂ => minimumValue J lambda) {J | J.mat.PosSemidef} :=
  fun _ hJ => continuousWithinAt_minimumValue_psd hJ hl

theorem continuousWithinAt_value_psd {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) :
    ContinuousWithinAt (fun K : HermitianMat (BlockIndex n) ℂ => value K lambda)
      {K | K.mat.PosSemidef} J :=
  (continuous_psi.comp pinching.continuous).continuousAt.continuousWithinAt.add
    (continuousWithinAt_minimumValue_psd hJ hl)

theorem continuousOn_value_psd {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0) :
    ContinuousOn (fun J : HermitianMat (BlockIndex n) ℂ => value J lambda) {J | J.mat.PosSemidef} :=
  fun _ hJ => continuousWithinAt_value_psd hJ hl

theorem regularization_posDef {J : HermitianMat k ℂ} (hJ : J.mat.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (J+t • 1).mat.PosDef := by
  change (J.mat+t • (1 : Matrix k k ℂ)).PosDef
  rw [add_comm]
  exact (Matrix.PosDef.one.smul (α := ℝ) ht).add_posSemidef hJ

/-- The actual PSD minimum value, not an assumed boundary extension, is the regularization limit. -/
theorem tendsto_value_regularization {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosSemidef) (hl : ∀ i, lambda i < 0) :
    Tendsto (fun t : ℝ => value (J+t • 1) lambda) (𝓝[>] 0) (𝓝 (value J lambda)) := by
  have hc : Continuous (fun t : ℝ => J+t • (1 : HermitianMat (BlockIndex n) ℂ)) := by fun_prop
  have ht : Tendsto (fun t : ℝ => J+t • (1 : HermitianMat (BlockIndex n) ℂ)) (𝓝[>] 0)
      (𝓝[{K | K.mat.PosSemidef}] J) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (regularization_posDef hJ ht).posSemidef
  exact (continuousWithinAt_value_psd hJ hl).tendsto.comp ht

/-- Concavity of the true minimized dual value includes every singular PSD input. -/
theorem concaveOn_value_psd {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0) :
    ConcaveOn ℝ {J : HermitianMat (BlockIndex n) ℂ | J.mat.PosSemidef}
      (fun J => value J lambda) := by
  constructor
  · intro J hJ K hK a b ha hb hab
    convert! (hJ.smul ha).add (hK.smul hb) using 1
  intro J hJ K hK a b ha hb hab
  have hC : (a • J+b • K).mat.PosSemidef := by
    convert! (hJ.smul ha).add (hK.smul hb) using 1
  have hL : Tendsto (fun t : ℝ => a*value (J+t • 1) lambda+
      b*value (K+t • 1) lambda) (𝓝[>] 0)
      (𝓝 (a*value J lambda+b*value K lambda)) :=
    (tendsto_const_nhds.mul (tendsto_value_regularization hJ hl)).add
      (tendsto_const_nhds.mul (tendsto_value_regularization hK hl))
  apply le_of_tendsto_of_tendsto hL (tendsto_value_regularization hC hl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hi := (concaveOn_value hl).2
    (regularization_posDef hJ ht) (regularization_posDef hK ht) ha hb hab
  have he : a • (J+t • 1)+b • (K+t • 1) = a • J+b • K+t • 1 := by
    calc
      _ = a • J+b • K+(a+b) • (t • (1 : HermitianMat (BlockIndex n) ℂ)) := by module
      _ = _ := by rw [hab,one_smul]
  simpa only [he,smul_eq_mul] using hi

end SchurEntropy.Optimized
