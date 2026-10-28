/-
Adapted and generalized to arbitrary finite block families from
KitaKen1/qubit-strong-additivity, lean/QubitAdditivity/BetaDual.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945.
Upstream code is licensed under the Apache License, Version 2.0.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt` for attribution and terms.
-/
import SchurEntropy.MultiBlockDiagonal
import QubitAdditivity.BetaDualExistence

set_option maxHeartbeats 100000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology RealInnerProductSpace

namespace SchurEntropy.Optimized
open QubitAdditivity QubitAdditivity.BetaPowers QubitAdditivity.BetaEntropy

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

abbrev Blocks (n : Fin m → ℕ) := ∀ i, HermitianMat (Fin (n i)) ℂ

def diagonal (W : Blocks n) : HermitianMat (BlockIndex n) ℂ :=
  ⟨Matrix.blockDiagonal' (fun i => (W i).mat),
    Matrix.isHermitian_blockDiagonal'_iff.mpr (fun i => (W i).H)⟩

@[simp] theorem diagonal_mat (W : Blocks n) :
    (diagonal W).mat = Matrix.blockDiagonal' (fun i => (W i).mat) := rfl

def diagonalLM : Blocks n →ₗ[ℝ] HermitianMat (BlockIndex n) ℂ where
  toFun := diagonal
  map_add' W Z := by
    apply HermitianMat.ext
    change Matrix.blockDiagonal' (fun i => (W i).mat + (Z i).mat) = _
    exact Matrix.blockDiagonal'_add (fun i => (W i).mat) (fun i => (Z i).mat)
  map_smul' c W := by
    apply HermitianMat.ext
    change Matrix.blockDiagonal' (fun i => c • (W i).mat) = _
    exact Matrix.blockDiagonal'_smul c (fun i => (W i).mat)

def diagonalCLM : Blocks n →L[ℝ] HermitianMat (BlockIndex n) ℂ :=
  (diagonalLM (n := n)).toContinuousLinearMap

@[simp] theorem diagonalCLM_apply (W : Blocks n) : diagonalCLM W = diagonal W := rfl

@[simp] theorem diagonal_add (W Z : Blocks n) : diagonal (W+Z) = diagonal W+diagonal Z :=
  diagonalLM.map_add W Z
@[simp] theorem diagonal_smul (c : ℝ) (W : Blocks n) : diagonal (c • W) = c • diagonal W :=
  diagonalLM.map_smul c W
@[simp] theorem diagonal_zero : diagonal (0 : Blocks n) = 0 := by
  exact (diagonalLM (n := n)).map_zero

def pinch (J : HermitianMat (BlockIndex n) ℂ) : Blocks n :=
  fun i => ⟨J.mat.submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)), J.H.submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))⟩

def pinchLM : HermitianMat (BlockIndex n) ℂ →ₗ[ℝ] Blocks n where
  toFun := pinch
  map_add' J K := by ext i a b; rfl
  map_smul' c J := by ext i a b; rfl

def pinchCLM : HermitianMat (BlockIndex n) ℂ →L[ℝ] Blocks n :=
  (pinchLM (n := n)).toContinuousLinearMap

@[simp] theorem pinchCLM_apply (J : HermitianMat (BlockIndex n) ℂ) : pinchCLM J = pinch J := rfl

@[simp] theorem pinch_diagonal (W : Blocks n) : pinch (diagonal W) = W := by
  funext i
  apply HermitianMat.ext
  ext a b
  change Matrix.blockDiagonal' (fun j => (W j).mat) ⟨i,a⟩ ⟨i,b⟩ = (W i).mat a b
  simp [Matrix.blockDiagonal'_apply]

theorem diagonal_injective : Function.Injective (diagonal (n := n)) :=
  Function.LeftInverse.injective pinch_diagonal

theorem trace_diagonal_mul (H : Blocks n) (X : BlockMatrix n) :
    ((diagonal H).mat * X).trace =
      ∑ i, ((H i).mat * X.submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))).trace := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sigma, diagonal,
    Matrix.blockDiagonal'_apply', Matrix.submatrix_apply]

theorem logarithm_diagonal (W : Blocks n) : logarithm (diagonal W).mat =
    Matrix.blockDiagonal' (fun i => logarithm (W i).mat) :=
  MultiBlock.cfc_diagonal _ (fun i => (W i).H) Real.log

theorem psi_diagonal (W : Blocks n) : psi (diagonal W) = ∑ i, psi (W i) := by
  simp only [psi_eq_trace]
  rw [logarithm_diagonal, trace_diagonal_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (Matrix.blockDiagonal' (fun i => logarithm (W i).mat)).submatrix
      (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))
      (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) = logarithm (W i).mat := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  rw [he]

def linearPenalty (lambda : Fin m → ℝ) : Blocks n →L[ℝ] ℝ :=
  ∑ i, (lambda i • BetaDual.traceHerm).comp (ContinuousLinearMap.proj i)

@[simp] theorem linearPenalty_apply (lambda : Fin m → ℝ) (W : Blocks n) :
    linearPenalty lambda W = ∑ i, lambda i * (W i).mat.trace.re := by
  simp [linearPenalty]

/-- The nonconstant part of the natural-log optimized deficit. -/
def objective (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) (W : Blocks n) : ℝ :=
  psi (diagonal W) - psi (J+diagonal W) - linearPenalty lambda W

def gradient (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ) (W : Blocks n) :
    Blocks n →L[ℝ] ℝ :=
  (psiGradient (diagonal W).mat).comp diagonalCLM -
    (psiGradient (J+diagonal W).mat).comp diagonalCLM - linearPenalty lambda

def positiveCone : Set (Blocks n) := {W | ∀ i, (W i).mat.PosSemidef}
def positiveInterior : Set (Blocks n) := {W | ∀ i, (W i).mat.PosDef}

theorem diagonal_posSemidef {W : Blocks n} (hW : W ∈ positiveCone) :
    (diagonal W).mat.PosSemidef := MultiBlock.diagonal_posSemidef hW

theorem diagonal_posDef {W : Blocks n} (hW : W ∈ positiveInterior) :
    (diagonal W).mat.PosDef := MultiBlock.diagonal_posDef hW

theorem total_posDef {J : HermitianMat (BlockIndex n) ℂ} (hJ : J.mat.PosDef)
    {W : Blocks n} (hW : W ∈ positiveCone) : (J+diagonal W).mat.PosDef :=
  hJ.add_posSemidef (diagonal_posSemidef hW)

theorem interior_subset_cone : positiveInterior (n := n) ⊆ positiveCone :=
  fun W hW i => (hW i).posSemidef

theorem hasFDerivAt_objective {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    {W : Blocks n} (hW : W ∈ positiveInterior) (hT : (J+diagonal W).mat.PosDef) :
    HasFDerivAt (objective J lambda) (gradient J lambda W) W := by
  have hd := (hasFDerivAt_psi (diagonal_posDef hW)).comp W
    (diagonalCLM (n := n)).hasFDerivAt
  have ht : HasFDerivAt (fun Z : Blocks n => J+diagonal Z) diagonalCLM W := by
    convert! (diagonalCLM (n := n)).hasFDerivAt.const_add J using 1
  convert! (hd.sub ((hasFDerivAt_psi hT).comp W ht)).sub
    (linearPenalty (n := n) lambda).hasFDerivAt using 1

def stationaryResidual (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (W : Blocks n) : Blocks n :=
  fun i => BetaDual.hermLog (W i) - pinch (BetaDual.hermLog (J+diagonal W)) i - lambda i • 1

theorem gradient_apply (J : HermitianMat (BlockIndex n) ℂ) (lambda : Fin m → ℝ)
    (W H : Blocks n) : gradient J lambda W H =
      ∑ i, ((H i).mat * (stationaryResidual J lambda W i).mat).trace.re := by
  simp only [gradient, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    psiGradient_apply, diagonalCLM_apply, linearPenalty_apply]
  rw [trace_diagonal_mul, trace_diagonal_mul, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : (logarithm (diagonal W).mat+1).submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) =
      logarithm (W i).mat+1 := by
    rw [logarithm_diagonal]
    ext a b
    simp [Matrix.submatrix_apply, Matrix.blockDiagonal'_apply, Matrix.one_apply]
  have ht : (logarithm (J+diagonal W).mat+1).submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) =
      (logarithm (J+diagonal W).mat).submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)) (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))+1 := by
    ext a b
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [hd, ht]
  exact (BetaDual.trace_mul_residual (H i).mat _ _ (lambda i)).symm

theorem stationaryResidual_eq_zero {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    {W : Blocks n} (hg : gradient J lambda W = 0) :
    stationaryResidual J lambda W = 0 := by
  let R := stationaryResidual J lambda W
  have he := congrArg (fun L : Blocks n →L[ℝ] ℝ => L R) hg
  simp only [gradient_apply, ContinuousLinearMap.zero_apply] at he
  have hs : ∑ i, inner ℝ (R i) (R i) = 0 := by
    change (∑ i, ((R i).mat * (R i).mat).trace.re) = 0 at he
    simp only [HermitianMat.inner_eq_re_trace]
    convert! he using 1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => real_inner_self_nonneg (x := R i))).mp hs
  funext i
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hz i (Finset.mem_univ i))

theorem positiveInterior_mem_nhds {W : Blocks n} (hW : W ∈ positiveInterior) :
    positiveInterior (n := n) ∈ 𝓝 W := by
  have h (i : Fin m) : ∀ᶠ Z : Blocks n in 𝓝 W, (Z i).mat.PosDef :=
    ((continuous_apply i).tendsto W).eventually (BetaLog.eventually_posDef (hW i))
  exact Filter.eventually_all.mpr h

theorem positiveCone_mem_nhds {W : Blocks n} (hW : W ∈ positiveInterior) :
    positiveCone (n := n) ∈ 𝓝 W :=
  Filter.mem_of_superset (positiveInterior_mem_nhds hW) interior_subset_cone

theorem stationarity_of_minOn_positiveCone {J : HermitianMat (BlockIndex n) ℂ}
    {lambda : Fin m → ℝ} {W : Blocks n} (hW : W ∈ positiveInterior)
    (hT : (J+diagonal W).mat.PosDef) (hmin : IsMinOn (objective J lambda) positiveCone W) :
    stationaryResidual J lambda W = 0 :=
  stationaryResidual_eq_zero ((hmin.isLocalMin (positiveCone_mem_nhds hW)).hasFDerivAt_eq_zero
    (hasFDerivAt_objective lambda hW hT))

@[simp] theorem diagonal_one : diagonal (1 : Blocks n) = 1 := by
  apply HermitianMat.ext
  exact Matrix.blockDiagonal'_one

theorem positiveInterior_of_diagonal_posDef {W : Blocks n} (hW : (diagonal W).mat.PosDef) :
    W ∈ positiveInterior := by
  intro i
  let e : Fin (n i) ↪ BlockIndex n := ⟨(fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)), @sigma_mk_injective (Fin m) (fun i => Fin (n i)) i⟩
  have h := BlockAlgebra.coordinateInclusion_compression_posDef e hW
  rw [BlockAlgebra.coordinateInclusion_compression] at h
  have he : (diagonal W).mat.submatrix e e = (W i).mat := by
    ext a b
    simp [e, diagonal, Matrix.submatrix_apply, Matrix.blockDiagonal'_apply]
  rwa [he] at h

def hessianRow (J : HermitianMat (BlockIndex n) ℂ) (W H : Blocks n) : Blocks n →L[ℝ] ℝ :=
  (psiHessianRow (diagonal W).mat (diagonal H) -
    psiHessianRow (J+diagonal W).mat (diagonal H)).comp diagonalCLM

@[simp] theorem hessianRow_apply (J : HermitianMat (BlockIndex n) ℂ) (W H K : Blocks n) :
    hessianRow J W H K = psiHessianRow (diagonal W).mat (diagonal H) (diagonal K) -
      psiHessianRow (J+diagonal W).mat (diagonal H) (diagonal K) := rfl

theorem hasFDerivAt_gradient_row {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    {W : Blocks n} (hW : W ∈ positiveInterior) (hT : (J+diagonal W).mat.PosDef) (H : Blocks n) :
    HasFDerivAt (fun Z : Blocks n => gradient J lambda Z H) (hessianRow J W H) W := by
  have hw := (hasFDerivAt_psiGradient_row (diagonal_posDef hW) (diagonal H)).comp W
    (diagonalCLM (n := n)).hasFDerivAt
  have hd : HasFDerivAt (fun Z : Blocks n => J+diagonal Z) diagonalCLM W := by
    convert! (diagonalCLM (n := n)).hasFDerivAt.const_add J using 1
  have ht := (hasFDerivAt_psiGradient_row hT (diagonal H)).comp W hd
  convert! (hw.sub ht).sub_const (linearPenalty lambda H) using 1

theorem hessianRow_self_pos {J : HermitianMat (BlockIndex n) ℂ} {W : Blocks n}
    (hJ : J.mat.PosDef) (hW : W ∈ positiveInterior) {H : Blocks n} (hH : H ≠ 0) :
    0 < hessianRow J W H H := by
  have hg : ((J+diagonal W).mat-(diagonal W).mat).PosDef := by
    simpa only [HermitianMat.mat_add,add_sub_cancel_right] using hJ
  have hn : diagonal H ≠ 0 := by
    intro hz
    apply hH
    exact diagonal_injective (hz.trans diagonal_zero.symm)
  exact BetaKMOrder.psiHessian_gap_pos (total_posDef hJ (interior_subset_cone hW))
    (diagonal_posDef hW) hg hn

end SchurEntropy.Optimized
