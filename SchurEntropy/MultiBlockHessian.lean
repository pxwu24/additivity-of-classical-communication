/-
Adapted for arbitrary finite block families from BetaKM.lean and BetaHessian.lean
in KitaKen1/qubit-strong-additivity, commit 90e61c463deb42067c109c46f048c6374dfc5945.
The upstream source is distributed under the Apache License, Version 2.0.
-/
import SchurEntropy.MultiBlockComparison
import QubitAdditivity.BetaResolvent

/-! # The eliminated curvature matrix for arbitrary finite blocks

All operator inequalities here are established for the actual Kubo–Mori
operators.  Logarithmic stationarity is explicit; existence and differentiation
of a minimizing noise matrix belong to the optimization modules.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace SchurEntropy.MultiBlock
open QubitAdditivity QubitAdditivity.BetaPowers
open BlockAlgebra

local instance hessianNorm {i j : Type*} [Fintype i] [Fintype j] :
    NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))
local instance hessianSpace {i j : Type*} [Fintype i] [Fintype j] :
    NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))
local instance hessianENorm {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

variable {m : ℕ} (n : Fin m → ℕ)
local notation "V" => blockInclusion n

def residual (T : BlockMatrix n) (W : Matrices n) :=
  km T - V * blockKM n W * Vᴴ

theorem blockKM_posDef {W : Matrices n} (hW : ∀ i, (W i).PosDef) : (blockKM n W).PosDef :=
  diagonal_posDef (fun i => BetaKM.km_posDef (hW i))

theorem continuous_pw_residual {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef) :
    Continuous (fun t => pw T t - V * blockPW n W t * Vᴴ) := by
  have hq := continuous_pw hT
  have hb := continuous_blockPW n hW
  fun_prop

theorem residual_eq_integral {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef) :
    residual n T W = ∫ t in (0 : ℝ)..1, pw T t - V * blockPW n W t * Vᴴ := by
  have he := (BetaBridge.compressionCLM Vᴴ).intervalIntegral_comp_comm
    (intervalIntegrable_blockPW n hW)
  have he' : (∫ t in (0 : ℝ)..1, V * blockPW n W t * Vᴴ) = V * blockKM n W * Vᴴ := by
    rw [← blockKM_eq_integral n hW] at he
    change (∫ t in (0 : ℝ)..1, Vᴴᴴ * blockPW n W t * Vᴴ) = Vᴴᴴ * blockKM n W * Vᴴ at he
    simpa only [conjTranspose_conjTranspose] using he
  have hc : Continuous (fun t => V * blockPW n W t * Vᴴ) := by
    have hb := continuous_blockPW n hW
    fun_prop
  rw [intervalIntegral.integral_sub (intervalIntegrable_pw hT) (hc.intervalIntegrable 0 1), he']
  rfl

theorem residual_posDef {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) : (residual n T W).PosDef := by
  rw [residual_eq_integral n hT hW]
  exact BetaKM.integral_posDef (continuous_pw_residual n hT hW)
    (fun _ ht => pw_residual_posDef n hT hW hgap ht)

theorem residual_compression (T : BlockMatrix n) (W : Matrices n) :
    Vᴴ * residual n T W * V = Vᴴ * km T * V - blockKM n W := by
  simp only [residual, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  calc
    _ = (Vᴴ * V) * blockKM n W * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [blockInclusion_isometry]; simp

theorem compression_gap_posSemidef {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) (μ : Fin m → ℂ)
    (hs : ∀ i, logarithm (W i) = diagonalBlock n (logarithm T) i + μ i • 1) :
    (blockKM n (gap n T W) - Vᴴ * residual n T W * V).PosSemidef := by
  have hk := km_of_stationarity n hT hW hgap μ hs
  have hc : Vᴴ * residual n T W * V ≤ blockKM n (gap n T W) := by
    rw [residual_compression]
    apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using hk
  exact Matrix.LE.le.posSemidef (sub_nonneg.mpr hc)

theorem inverseKM_compression_gap_posDef {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) :
    ((blockKM n W)⁻¹ - Vᴴ * (km T)⁻¹ * V).PosDef := by
  have hg : (km T - Vᴴᴴ * blockKM n W * Vᴴ).PosDef := by
    simpa only [residual, conjTranspose_conjTranspose] using residual_posDef n hT hW hgap
  simpa only [conjTranspose_conjTranspose] using
    BetaResolvent.inverse_compression_strict_posDef (blockKM n W) (km T) Vᴴ
      (blockKM_posDef n hW) (BetaKM.km_posDef hT) hg

/-- Nonpositivity of the exact matrix obtained by eliminating the noise
directions from the entropy Hessian at a logarithmically stationary point. -/
theorem eliminated_expression_nonpos {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) (μ : Fin m → ℂ)
    (hs : ∀ i, logarithm (W i) = diagonalBlock n (logarithm T) i + μ i • 1) :
    V * (blockKM n (gap n T W))⁻¹ * Vᴴ - (km T)⁻¹ -
      (km T)⁻¹ * V * ((blockKM n W)⁻¹ - Vᴴ * (km T)⁻¹ * V)⁻¹ * Vᴴ * (km T)⁻¹ ≤ 0 := by
  exact BetaOrder.eliminatedHessian_nonpos (km T) (blockKM n W) (blockKM n (gap n T W)) V
    (BetaKM.km_posDef hT).isUnit (blockKM_posDef n hW).isUnit
    (inverseKM_compression_gap_posDef n hT hW hgap).isUnit
    (residual_posDef n hT hW hgap) (blockKM_posDef n (gap_posDef n hgap))
    (compression_gap_posSemidef n hT hW hgap μ hs)

end SchurEntropy.MultiBlock
