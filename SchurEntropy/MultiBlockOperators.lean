/-
Adapted for arbitrary finite block families from BetaBridge.lean, BetaBlocks.lean, and BetaStrict.lean
in KitaKen1/qubit-strong-additivity, commit 90e61c463deb42067c109c46f048c6374dfc5945.
The upstream source is distributed under the Apache License, Version 2.0.
-/
import SchurEntropy.MultiBlockDiagonal
import QubitAdditivity.BetaStrict

/-! # PW operators on an arbitrary finite block algebra

The scalar spectral-power and operator-curve facts come from the pinned
`qubitStrongAdditivity` dependency.  The block assembly and compression here
allow an arbitrary number of blocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace SchurEntropy.MultiBlock
open QubitAdditivity QubitAdditivity.BetaPowers
open BlockAlgebra

local instance matrixNorm {i j : Type*} [Fintype i] [Fintype j] :
    NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))
local instance matrixSpace {i j : Type*} [Fintype i] [Fintype j] :
    NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))
local instance matrixENorm {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))
local instance familyENorm {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] : ENormedAddMonoid (∀ i, Matrix (κ i) (κ i) ℂ) :=
  NormedAddGroup.toENormedAddMonoid

variable {m : ℕ} (n : Fin m → ℕ)
abbrev Matrices := ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ

def diagonalCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] :
    (∀ i, Matrix (κ i) (κ i) ℂ) →L[ℝ] Matrix (Σ i, κ i) (Σ i, κ i) ℂ :=
  (diagonalHom (κ := κ)).toAlgHom.toLinearMap.toContinuousLinearMap

@[simp] theorem diagonalCLM_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (A : ∀ i, Matrix (κ i) (κ i) ℂ) : diagonalCLM A = Matrix.blockDiagonal' A := rfl

theorem power_diagonal (W : Matrices n) (hW : ∀ i, (W i).IsHermitian) (t : ℝ) :
    power (Matrix.blockDiagonal' W) t = Matrix.blockDiagonal' (fun i => power (W i) t) :=
  cfc_diagonal W hW _

theorem logarithm_diagonal (W : Matrices n) (hW : ∀ i, (W i).IsHermitian) :
    logarithm (Matrix.blockDiagonal' W) = Matrix.blockDiagonal' (fun i => logarithm (W i)) :=
  cfc_diagonal W hW _

def blockPW (W : Matrices n) (t : ℝ) :
    Matrix (DiagonalUnitIndex n) (DiagonalUnitIndex n) ℂ :=
  Matrix.blockDiagonal' (fun i => pw (W i) t)

def blockKM (W : Matrices n) : Matrix (DiagonalUnitIndex n) (DiagonalUnitIndex n) ℂ :=
  Matrix.blockDiagonal' (fun i => km (W i))

theorem blockPW_generator_commute (W : Matrices n) (t : ℝ) :
    Commute (blockPW n W t) (blockGenerator n (fun i => logarithm (W i))) := by
  change Matrix.blockDiagonal' (fun i => pw (W i) t) *
      Matrix.blockDiagonal' (fun i => BetaOperators.generator (logarithm (W i))) =
    Matrix.blockDiagonal' (fun i => BetaOperators.generator (logarithm (W i))) *
      Matrix.blockDiagonal' (fun i => pw (W i) t)
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext i
  exact (pw_generator_commute (W i) t).eq

theorem hasDerivAt_blockPW {W : Matrices n} (hW : ∀ i, (W i).PosDef) (t : ℝ) :
    HasDerivAt (blockPW n W)
      (blockGenerator n (fun i => logarithm (W i)) * blockPW n W t) t := by
  have hd := hasDerivAt_pi.2 (fun i => hasDerivAt_pw (hW i) t)
  have hh := (diagonalCLM (κ := fun i => Fin (n i) × Fin (n i))).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun u => Matrix.blockDiagonal' (fun i => pw (W i) u))
    (Matrix.blockDiagonal' (fun i => BetaOperators.generator (logarithm (W i))) *
      Matrix.blockDiagonal' (fun i => pw (W i) t)) t
  rw [← Matrix.blockDiagonal'_mul]
  exact hh

theorem continuous_blockPW {W : Matrices n} (hW : ∀ i, (W i).PosDef) :
    Continuous (blockPW n W) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_blockPW n hW t).continuousAt)

theorem intervalIntegrable_blockPW {W : Matrices n} (hW : ∀ i, (W i).PosDef) :
    IntervalIntegrable (blockPW n W) MeasureTheory.volume 0 1 :=
  (continuous_blockPW n hW).intervalIntegrable 0 1

theorem blockKM_eq_integral {W : Matrices n} (hW : ∀ i, (W i).PosDef) :
    blockKM n W = ∫ t in (0 : ℝ)..1, blockPW n W t := by
  have hc : Continuous (fun t : ℝ => fun i => pw (W i) t) :=
    continuous_pi (fun i => continuous_pw (hW i))
  have hi : IntervalIntegrable (fun t : ℝ => fun i => pw (W i) t) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable (0 : ℝ) 1
  have he : (∫ t in (0 : ℝ)..1, fun i => pw (W i) t) = fun i => km (W i) := by
    funext i
    let P : (∀ j, Matrix (Fin (n j) × Fin (n j)) (Fin (n j) × Fin (n j)) ℂ) →L[ℝ]
        Matrix (Fin (n i) × Fin (n i)) (Fin (n i) × Fin (n i)) ℂ := ContinuousLinearMap.proj i
    exact (P.intervalIntegral_comp_comm hi).symm
  have hh := (diagonalCLM (κ := fun i => Fin (n i) × Fin (n i))).intervalIntegral_comp_comm hi
  rw [he] at hh
  exact hh.symm

theorem pw_diagonal_compression (W : Matrices n) (hW : ∀ i, (W i).IsHermitian) (t : ℝ) :
    (blockInclusion n)ᴴ * pw (Matrix.blockDiagonal' W) t * blockInclusion n = blockPW n W t := by
  rw [blockInclusion, coordinateInclusion_compression, pw_eq_kronecker,
    power_diagonal n W hW, power_diagonal n W hW]
  ext ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hij : i = j
  · subst j
    simp [blockPW, pw_eq_kronecker, kroneckerMap_apply]
  · simp [blockPW, pw_eq_kronecker, kroneckerMap_apply,
      Matrix.blockDiagonal'_apply_ne, hij]

theorem pw_diagonal_reduces (W : Matrices n) (hW : ∀ i, (W i).IsHermitian) (t : ℝ) :
    pw (Matrix.blockDiagonal' W) t * blockInclusion n = blockInclusion n * blockPW n W t := by
  rw [pw_eq_kronecker, power_diagonal n W hW, power_diagonal n W hW]
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩ ⟨k, c, d⟩
  simp [blockInclusion, coordinateInclusion, diagonalUnitEmbedding,
    Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_prod_type,
    blockPW, pw_eq_kronecker, kroneckerMap_apply, Matrix.one_apply]
  rw [Fintype.sum_eq_single k]
  · by_cases hik : i = k
    · subst k
      by_cases hji : j = i
      · subst j
        simp [Prod.mk.injEq, kroneckerMap_apply, ite_and]
      · simp [Prod.mk.injEq,
          Matrix.blockDiagonal'_apply_ne, hji]
    · simp [Prod.mk.injEq,
        Matrix.blockDiagonal'_apply_ne, hik]
  · intro x hx
    simp [Matrix.blockDiagonal'_apply_ne, hx]

theorem pw_diagonal_residual_posSemidef {W : Matrices n} (hW : ∀ i, (W i).PosDef) (t : ℝ) :
    (pw (Matrix.blockDiagonal' W) t -
      blockInclusion n * blockPW n W t * (blockInclusion n)ᴴ).PosSemidef := by
  let V := blockInclusion n
  let Q := pw (Matrix.blockDiagonal' W) t
  have hfull := diagonal_posDef hW
  have hV : Vᴴ * V = 1 := blockInclusion_isometry n
  have hred : Q * V = V * blockPW n W t := pw_diagonal_reduces n W (fun i => (hW i).1) t
  have hh := (pw_posDef hfull t).posSemidef.conjTranspose_mul_mul_same (1 - V * Vᴴ)
  convert hh using 1
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one]
  have hright : Q * (V * Vᴴ) = V * blockPW n W t * Vᴴ := by
    rw [← Matrix.mul_assoc, hred]
  have hleft : V * Vᴴ * Q = V * blockPW n W t * Vᴴ := by
    have hc := congrArg Matrix.conjTranspose hright
    have hb : (blockPW n W t).IsHermitian :=
      Matrix.isHermitian_blockDiagonal'_iff.mpr (fun i => (pw_posDef (hW i) t).1)
    simpa [conjTranspose_mul, (pw_posDef hfull t).1.eq, hb.eq, V, Q, Matrix.mul_assoc] using hc
  have he : (V * blockPW n W t * Vᴴ) * (V * Vᴴ) = V * blockPW n W t * Vᴴ := by
    calc
      _ = V * blockPW n W t * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  change Q - V * blockPW n W t * Vᴴ = _
  rw [hright, hleft, he]
  abel

theorem pw_residual_posDef {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (pw T t - blockInclusion n * blockPW n W t * (blockInclusion n)ᴴ).PosDef := by
  have hp := BetaStrict.pw_sub_posDef hT (diagonal_posDef hW) hgap ht
  have hq := pw_diagonal_residual_posSemidef n hW t
  convert hp.add_posSemidef hq using 1
  abel

end SchurEntropy.MultiBlock
