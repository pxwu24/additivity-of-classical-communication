/-
Adapted for arbitrary finite block families from BetaBridge.lean, BetaEndpoints.lean, and BetaPWBound.lean
in KitaKen1/qubit-strong-additivity, commit 90e61c463deb42067c109c46f048c6374dfc5945.
The upstream source is distributed under the Apache License, Version 2.0.
-/
import SchurEntropy.MultiBlockOperators
import QubitAdditivity.BetaBarrier
import QubitAdditivity.BetaKM

/-! # Stationary PW and Kubo–Mori comparison for arbitrary finite blocks -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace SchurEntropy.MultiBlock
open QubitAdditivity QubitAdditivity.BetaPowers
open BlockAlgebra

local instance comparisonNorm {i j : Type*} [Fintype i] [Fintype j] :
    NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))
local instance comparisonSpace {i j : Type*} [Fintype i] [Fintype j] :
    NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))
local instance comparisonENorm {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

variable {m : ℕ} (n : Fin m → ℕ)
local notation "V" => blockInclusion n

def curve (T : BlockMatrix n) (W : Matrices n) (t : ℝ) :=
  Vᴴ * pw T t * V - blockPW n W t

def curveFirst (T : BlockMatrix n) (W : Matrices n) (t : ℝ) :=
  Vᴴ * pw T t * generator (logarithm T) * V -
    blockPW n W t * blockGenerator n (fun i => logarithm (W i))

def curveSecond (T : BlockMatrix n) (W : Matrices n) (t : ℝ) :=
  Vᴴ * pw T t * generator (logarithm T) * generator (logarithm T) * V -
    blockGenerator n (fun i => logarithm (W i)) * blockPW n W t *
      blockGenerator n (fun i => logarithm (W i))

theorem hasDerivAt_curve {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef) (t : ℝ) :
    HasDerivAt (curve n T W) (curveFirst n T W t) t := by
  have hp : HasDerivAt (pw T) (pw T t * generator (logarithm T)) t := by
    change HasDerivAt (pw T) (pw T t * BetaOperators.generator (logarithm T)) t
    simpa only [(pw_generator_commute T t).eq] using hasDerivAt_pw hT t
  have hb : HasDerivAt (blockPW n W)
      (blockPW n W t * blockGenerator n (fun i => logarithm (W i))) t := by
    simpa only [(blockPW_generator_commute n W t).eq] using hasDerivAt_blockPW n hW t
  have hc := BetaBridge.hasDerivAt_coordinateCompression (diagonalUnitEmbedding n) hp
  convert! hc.sub hb using 1
  simp only [curveFirst, blockInclusion, Matrix.mul_assoc]
  all_goals rfl

theorem hasDerivAt_curveFirst {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef) (t : ℝ) :
    HasDerivAt (curveFirst n T W) (curveSecond n T W t) t := by
  have hp : HasDerivAt (pw T) (pw T t * generator (logarithm T)) t := by
    change HasDerivAt (pw T) (pw T t * BetaOperators.generator (logarithm T)) t
    simpa only [(pw_generator_commute T t).eq] using hasDerivAt_pw hT t
  have hq := OpenAICalculus.hasDerivAt_matrix_mul hp
    (hasDerivAt_const t (generator (logarithm T)))
  have hb := OpenAICalculus.hasDerivAt_matrix_mul (hasDerivAt_blockPW n hW t)
    (hasDerivAt_const t (blockGenerator n (fun i => logarithm (W i))))
  have hc := BetaBridge.hasDerivAt_coordinateCompression (diagonalUnitEmbedding n) hq
  convert! hc.sub hb using 1 <;>
    simp only [curveSecond, blockInclusion, coordinateInclusion,
      BetaOperators.coordinateInclusion,
      Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  all_goals first | rfl | (ext u; simp only [curveFirst, Pi.sub_apply, blockInclusion, coordinateInclusion,
      Matrix.mul_assoc])

theorem curve_posDef {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (curve n T W t).PosDef := by
  have hh := blockInclusion_compression_posDef n (pw_residual_posDef n hT hW hgap ht)
  have he : Vᴴ * (pw T t - V * blockPW n W t * Vᴴ) * V = curve n T W t := by
    rw [Matrix.mul_sub, Matrix.sub_mul, curve]
    congr 1
    calc
      _ = (Vᴴ * V) * blockPW n W t * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = blockPW n W t := by rw [blockInclusion_isometry]; simp
  rwa [he] at hh

theorem stationaryGram_pw (T : BlockMatrix n) (W : Matrices n) (μ : Fin m → ℂ) (t : ℝ)
    (hs : ∀ i, logarithm (W i) = diagonalBlock n (logarithm T) i + μ i • 1)
    (hD : (pw T t - V * blockPW n W t * Vᴴ).PosSemidef) :
    (Matrix.fromBlocks (curve n T W t) (curveFirst n T W t)
      (curveFirst n T W t) (curveSecond n T W t)).PosSemidef :=
  BetaCore.stationaryGram_posSemidef (pw T t) (generator (logarithm T))
    (blockPW n W t) (blockGenerator n (fun i => logarithm (W i))) V
    (blockInclusion_isometry n) (generator_isHermitian (logarithm_isHermitian T))
    (pw_generator_commute T t).eq (blockPW_generator_commute n W t).eq
    (generator_compression_of_stationarity n (logarithm T) _ μ hs) hD

theorem left_compression (T : BlockMatrix n) :
    Vᴴ * BetaOperators.left T * V =
      Matrix.blockDiagonal' (fun i => BetaOperators.left (diagonalBlock n T i)) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hij : i = j
  · subst j
    simp [BetaOperators.left, diagonalBlock, kroneckerMap_apply, Matrix.one_apply]
  · simp [BetaOperators.left, diagonalBlock, kroneckerMap_apply,
      Matrix.blockDiagonal'_apply_ne, hij]

theorem right_compression (T : BlockMatrix n) :
    Vᴴ * BetaOperators.right T * V =
      Matrix.blockDiagonal' (fun i => BetaOperators.right (diagonalBlock n T i)) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hij : i = j
  · subst j
    simp [BetaOperators.right, diagonalBlock, kroneckerMap_apply, Matrix.one_apply]
  · simp [BetaOperators.right, diagonalBlock, kroneckerMap_apply,
      Matrix.blockDiagonal'_apply_ne, hij]

def gap (T : BlockMatrix n) (W : Matrices n) : Matrices n :=
  fun i => diagonalBlock n T i - W i

theorem gap_posDef {T : BlockMatrix n} {W : Matrices n}
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) (i : Fin m) : (gap n T W i).PosDef := by
  have h := hgap.submatrix (show Function.Injective (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))
    from by intro a b hab; simpa using hab)
  convert h using 1
  ext a b
  simp [gap, diagonalBlock]

theorem curve_zero {T : BlockMatrix n} {W : Matrices n}
    (hT : T.IsHermitian) (hW : ∀ i, (W i).IsHermitian) :
    curve n T W 0 = blockPW n (gap n T W) 0 := by
  rw [curve, pw_zero hT, right_compression]
  have hg (i : Fin m) : (gap n T W i).IsHermitian :=
    (hT.submatrix _).sub (hW i)
  simp only [blockPW, pw_zero (hW _), pw_zero (hg _), ← Matrix.blockDiagonal'_sub]
  apply congrArg Matrix.blockDiagonal'
  funext i
  ext a b
  simp [gap, BetaOperators.right, kroneckerMap_apply, mul_sub]

theorem curve_one {T : BlockMatrix n} {W : Matrices n}
    (hT : T.IsHermitian) (hW : ∀ i, (W i).IsHermitian) :
    curve n T W 1 = blockPW n (gap n T W) 1 := by
  rw [curve, pw_one hT, left_compression]
  have hg (i : Fin m) : (gap n T W i).IsHermitian :=
    (hT.submatrix _).sub (hW i)
  simp only [blockPW, pw_one (hW _), pw_one (hg _), ← Matrix.blockDiagonal'_sub]
  apply congrArg Matrix.blockDiagonal'
  funext i
  ext a b
  simp [gap, BetaOperators.left, kroneckerMap_apply, sub_mul]

/-- The comparison follows from positivity, actual logarithmic stationarity,
and the certified matrix-curve barrier theorem. -/
theorem pw_of_stationarity {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) (μ : Fin m → ℂ)
    (hs : ∀ i, logarithm (W i) = diagonalBlock n (logarithm T) i + μ i • 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Vᴴ * pw T t * V ≤ blockPW n W t + blockPW n (gap n T W) t := by
  have hP := gap_posDef n hgap
  have hQ : ∀ t, (blockPW n (gap n T W) t).PosDef :=
    fun t => diagonal_posDef (fun i => pw_posDef (hP i) t)
  have hK : (blockGenerator n (fun i => logarithm (gap n T W i))).IsHermitian :=
    Matrix.isHermitian_blockDiagonal'_iff.mpr
      (fun i => generator_isHermitian (logarithm_isHermitian _))
  have hz : curve n T W 0 ≤ blockPW n (gap n T W) 0 :=
    le_of_eq (curve_zero n hT.1 (fun i => (hW i).1))
  have ho : curve n T W 1 ≤ blockPW n (gap n T W) 1 :=
    le_of_eq (curve_one n hT.1 (fun i => (hW i).1))
  have hh := BetaBarrier.le_of_exponential (curve n T W) (curveFirst n T W)
    (curveSecond n T W) (blockPW n (gap n T W))
    (blockGenerator n (fun i => logarithm (gap n T W i)))
    (hasDerivAt_curve n hT hW) (hasDerivAt_curveFirst n hT hW)
    (hasDerivAt_blockPW n hP)
    (fun _ ht => (curve_posDef n hT hW hgap ht).1) hQ hK
    (fun t => (blockPW_generator_commute n (gap n T W) t).eq.symm)
    (fun t ht => stationaryGram_pw n T W μ t hs
      (pw_residual_posDef n hT hW hgap ⟨ht.1.le, ht.2.le⟩).posSemidef) hz ho
  intro t ht
  have hi := hh t ht
  change Vᴴ * pw T t * V - blockPW n W t ≤ blockPW n (gap n T W) t at hi
  simpa only [add_comm] using (sub_le_iff_le_add).mp hi

theorem km_of_stationarity {T : BlockMatrix n} {W : Matrices n}
    (hT : T.PosDef) (hW : ∀ i, (W i).PosDef)
    (hgap : (T - Matrix.blockDiagonal' W).PosDef) (μ : Fin m → ℂ)
    (hs : ∀ i, logarithm (W i) = diagonalBlock n (logarithm T) i + μ i • 1) :
    Vᴴ * km T * V ≤ blockKM n W + blockKM n (gap n T W) := by
  have hP := gap_posDef n hgap
  have hc := (BetaBridge.compressionCLM V).continuous.comp (continuous_pw hT)
  have hh := BetaBridge.intervalIntegral_mono_on (hc.intervalIntegrable 0 1)
    ((intervalIntegrable_blockPW n hW).add (intervalIntegrable_blockPW n hP))
    (pw_of_stationarity n hT hW hgap μ hs)
  simp only [Function.comp_def] at hh
  calc
    _ = ∫ t in (0 : ℝ)..1, BetaBridge.compressionCLM V (pw T t) := by
      convert! ((BetaBridge.compressionCLM V).intervalIntegral_comp_comm
        (intervalIntegrable_pw hT)).symm using 1
    _ ≤ ∫ t in (0 : ℝ)..1, blockPW n W t + blockPW n (gap n T W) t := hh
    _ = _ := by
      rw [intervalIntegral.integral_add (intervalIntegrable_blockPW n hW)
        (intervalIntegrable_blockPW n hP), ← blockKM_eq_integral n hW,
        ← blockKM_eq_integral n hP]

end SchurEntropy.MultiBlock
