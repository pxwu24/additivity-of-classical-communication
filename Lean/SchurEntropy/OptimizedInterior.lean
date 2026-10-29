/-
Adapted from KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/BetaDualInterior.lean (Apache-2.0).
Changes generalize two blocks to a finite dependent family.
See third_party/Apache-2.0.txt and third_party/NOTICE.
-/
import SchurEntropy.OptimizedExistence
import QubitAdditivity.BetaBoundaryEntropy

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaEntropy

@[reducible] private local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] private local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] private local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule

variable {m : ℕ} {n : Fin m → ℕ}

def line (W H : Blocks n) (t : ℝ) : Blocks n := W+t • H

theorem continuous_line (W H : Blocks n) : Continuous (line W H) := by
  unfold line
  fun_prop

theorem hasDerivAt_line (W H : Blocks n) (t : ℝ) : HasDerivAt (line W H) H t := by
  convert! ((hasDerivAt_id t).smul_const H).const_add W using 1 <;> simp

def correction (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) (W : Blocks n) : ℝ :=
  -psi (J+diagonal W)-linearPenalty lambda W

def correctionGradient (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) (W : Blocks n) :
    Blocks n →L[ℝ] ℝ := -(psiGradient (J+diagonal W).mat).comp diagonalCLM-linearPenalty lambda

theorem objective_eq_correction (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (W : Blocks n) : objective J lambda W = psi (diagonal W)+correction J lambda W := by
  unfold objective correction
  ring

theorem hasFDerivAt_correction {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    {W : Blocks n} (hT : (J+diagonal W).mat.PosDef) :
    HasFDerivAt (correction J lambda) (correctionGradient J lambda W) W := by
  have hl := (diagonalCLM (n := n)).hasFDerivAt (x := W) |>.const_add J
  have hd := (hasFDerivAt_psi hT).comp W hl
  convert! hd.neg.sub ((linearPenalty lambda).hasFDerivAt (x := W)) using 1

/-- A scalar identity perturbation excludes every singular minimizing block at once. -/
theorem positiveInterior_of_minOn {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) {W : Blocks n} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda) positiveCone W) : W ∈ positiveInterior := by
  apply positiveInterior_of_diagonal_posDef
  by_contra hnot
  let g : ℝ → ℝ := fun t => correction J lambda (line W 1 t)
  have ht : (J+diagonal (line W 1 0)).mat.PosDef := by
    simpa [line] using total_posDef hJ hW
  have hd : HasDerivAt g (correctionGradient J lambda W 1) 0 := by
    convert! (hasFDerivAt_correction lambda ht).comp_hasDerivAt 0
      (hasDerivAt_line W 1 0) using 1 <;> simp only [line,zero_smul,add_zero]
  obtain ⟨t,htp,hi⟩ := BetaBoundaryEntropy.exists_boundary_descent (diagonal_posSemidef hW) hnot hd
  have hp : line W 1 t ∈ positiveCone := by
    intro i
    exact (hW i).add (Matrix.PosDef.one.posSemidef.smul htp.le)
  have he (t : ℝ) : objective J lambda (line W 1 t) = psi (diagonal W+t • 1)+g t := by
    rw [objective_eq_correction]
    simp [line,g]
  have hi' : objective J lambda (line W 1 t) < objective J lambda W := by
    have hbase : objective J lambda W = psi (diagonal W)+g 0 := by simpa [line] using he 0
    rw [he,hbase]
    exact hi
  exact (not_lt_of_ge (hmin hp)) hi'

theorem stationarity_of_minOn {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) {W : Blocks n} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda) positiveCone W) : stationaryResidual J lambda W = 0 :=
  stationarity_of_minOn_positiveCone (positiveInterior_of_minOn hJ hW hmin) (total_posDef hJ hW) hmin

end SchurEntropy.Optimized
