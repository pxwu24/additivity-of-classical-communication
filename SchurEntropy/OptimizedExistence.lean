/-
Adapted from KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/BetaDualExistence.lean (Apache-2.0).
Changes generalize two blocks to a finite dependent family.
See third_party/Apache-2.0.txt and third_party/NOTICE.
-/
import SchurEntropy.OptimizedDefinitions

set_option maxHeartbeats 800000
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

variable {m : ℕ} {n : Fin m → ℕ}

theorem continuous_objective (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) :
    Continuous (objective J lambda) := by
  unfold objective
  exact ((BetaDualExistence.continuous_psi.comp (diagonalCLM (n := n)).continuous).sub
    (BetaDualExistence.continuous_psi.comp
      ((continuous_const (y := J)).add (diagonalCLM (n := n)).continuous))).sub
      (linearPenalty (n := n) lambda).continuous

theorem isClosed_positiveCone : IsClosed (positiveCone (n := n)) := by
  have h (i : Fin m) := (HermitianMat.isClosed_nonneg (n := Fin (n i)) (𝕜 := ℂ)).preimage
    (continuous_apply i : Continuous (fun W : Blocks n => W i))
  convert! isClosed_iInter h using 1
  ext W
  simp [positiveCone, HermitianMat.zero_le_iff]

def blockTrace (W : Blocks n) : ℝ := ∑ i, (W i).mat.trace.re

theorem continuous_blockTrace : Continuous (blockTrace (n := n)) := by
  apply continuous_finsetSum
  intro i _
  exact (BetaDual.traceHerm (k := Fin (n i))).continuous.comp (continuous_apply i)

theorem trace_diagonal (W : Blocks n) : (diagonal W).mat.trace.re = blockTrace W := by
  simp [blockTrace, diagonal, Matrix.trace, Fintype.sum_sigma, Complex.re_sum]

theorem trace_nonneg {i : Fin m} {W : Blocks n} (hW : W ∈ positiveCone) :
    0 ≤ (W i).mat.trace.re :=
  (norm_nonneg (W i)).trans (BetaDualExistence.norm_le_trace (hW i))

theorem blockTrace_nonneg {W : Blocks n} (hW : W ∈ positiveCone) : 0 ≤ blockTrace W :=
  Finset.sum_nonneg (fun i _ => trace_nonneg (i := i) hW)

theorem norm_le_blockTrace {W : Blocks n} (hW : W ∈ positiveCone) : ‖W‖ ≤ blockTrace W := by
  apply (pi_norm_le_iff_of_nonneg (blockTrace_nonneg hW)).mpr
  intro i
  exact (BetaDualExistence.norm_le_trace (hW i)).trans
    (Finset.single_le_sum (fun j _ => trace_nonneg (i := j) hW) (Finset.mem_univ i))

theorem isCompact_traceSublevel (R : ℝ) :
    IsCompact {W : Blocks n | W ∈ positiveCone ∧ blockTrace W ≤ R} := by
  have hc : IsClosed {W : Blocks n | W ∈ positiveCone ∧ blockTrace W ≤ R} :=
    isClosed_positiveCone.inter (isClosed_Iic.preimage continuous_blockTrace)
  apply Metric.isCompact_of_isClosed_isBounded hc
  apply (Metric.isBounded_closedBall (x := (0 : Blocks n)) (r := R)).subset
  intro W hW
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_blockTrace hW.1).trans hW.2

theorem penalty_lower_bound {lambda : Fin m → ℝ} {c : ℝ}
    (hc : ∀ i, c ≤ -lambda i) {W : Blocks n} (hW : W ∈ positiveCone) :
    c*blockTrace W ≤ -linearPenalty lambda W := by
  rw [blockTrace, Finset.mul_sum, linearPenalty_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa using mul_le_mul_of_nonneg_right (hc i) (trace_nonneg hW)

theorem objective_lower_bound {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ} {c : ℝ}
    (hJ : J.mat.PosDef) (hc : ∀ i, c ≤ -lambda i) {W : Blocks n} (hW : W ∈ positiveCone) :
    c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      objective J lambda W := by
  have hT : (diagonal W+J).mat.PosDef := by
    rw [add_comm]
    exact total_posDef hJ hW
  have hi := BetaDualExistence.psi_increment_le_trace (diagonal_posSemidef hW) hJ.posSemidef hT
  have ht : (diagonal W+J).mat.trace.re = blockTrace W+J.mat.trace.re := by
    change ((diagonal W).mat+J.mat).trace.re = _
    rw [Matrix.trace_add, Complex.add_re, trace_diagonal]
  rw [ht, add_comm (diagonal W) J] at hi
  have hp := penalty_lower_bound hc hW
  unfold objective
  linarith

theorem exists_uniform_positive {lambda : Fin m → ℝ} (hl : ∀ i, lambda i < 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ -lambda i := by
  have h : ∀ s : Finset (Fin m), ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c ≤ -lambda i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨c, hc, hs⟩ := ih
      refine ⟨min c (-lambda i), lt_min hc (neg_pos.mpr (hl i)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨c, hc, hs⟩ := h Finset.univ
  exact ⟨c, hc, fun i => hs i (Finset.mem_univ i)⟩

theorem objective_eventually_ge {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) (a : ℝ) :
    ∀ᶠ W in cocompact (Blocks n) ⊓ 𝓟 positiveCone, a ≤ objective J lambda W := by
  obtain ⟨c, hc, hcl⟩ := exists_uniform_positive hl
  rcases eventually_atTop.1
    ((BetaDualExistence.tendsto_scalar_lower_bound c J.mat.trace.re hc).eventually_ge_atTop a)
    with ⟨R,hR⟩
  rw [eventually_inf_principal]
  filter_upwards [(isCompact_traceSublevel (n := n) R).compl_mem_cocompact] with W houtside hW
  have hlarge : R < blockTrace W := by
    by_contra! hsmall
    exact houtside ⟨hW,hsmall⟩
  exact (hR (blockTrace W) hlarge.le).trans (objective_lower_bound hJ hcl hW)

theorem exists_minOn_positiveCone {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    ∃ W ∈ positiveCone, IsMinOn (objective J lambda) positiveCone W := by
  apply (continuous_objective J lambda).continuousOn.exists_isMinOn' isClosed_positiveCone
    (x₀ := (0 : Blocks n))
  · intro i
    exact Matrix.PosSemidef.zero
  · exact objective_eventually_ge hJ hl _

end SchurEntropy.Optimized
