import SchurEntropy.Definitions
import QuantumInfo.ForMathlib.HermitianMat.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Matrix.Block

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace SchurEntropy

theorem posSemidef_blockDiagonal {m : ℕ} {n : Fin m → ℕ}
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ)
    (hA : ∀ i, (A i).PosSemidef) :
    (Matrix.blockDiagonal' A).PosSemidef := by
  let R := fun i => CFC.sqrt (A i)
  have heq : (Matrix.blockDiagonal' R).conjTranspose * Matrix.blockDiagonal' R =
      Matrix.blockDiagonal' A := by
    rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    change star (CFC.sqrt (A i)) * CFC.sqrt (A i) = A i
    rw [(CFC.sqrt_nonneg (A i)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self (A i) (hA i).nonneg
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Each positive block is at most its trace times the identity. -/
theorem blockTrace_smul_one_sub_posSemidef {m : ℕ} {n : Fin m → ℕ}
    {W : BlockMatrix n} (hW : W.PosSemidef) (i : Fin m) :
    ((blockTrace n W i) • (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) -
      W.submatrix (Sigma.mk i) (Sigma.mk i)).PosSemidef := by
  let B : HermitianMat (Fin (n i)) ℂ :=
    ⟨W.submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))
      (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n)),
      (hW.submatrix (fun a : Fin (n i) => (⟨i, a⟩ : BlockIndex n))).isHermitian⟩
  have hB : 0 ≤ B := HermitianMat.zero_le_iff.mpr (hW.submatrix (Sigma.mk i))
  have htrace : B.trace = blockTrace n W i := by
    rw [HermitianMat.trace_eq_re_trace]
    simp [B, blockTrace, Matrix.trace, Matrix.diag_apply]
  have hb := HermitianMat.le_iff.mp (HermitianMat.le_trace_smul_one hB)
  simpa [B, HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
    htrace] using hb

/-- A positive block-diagonal noise matrix is bounded by its block traces. -/
theorem blockMultiplier_blockTrace_sub_posSemidef {m : ℕ} {n : Fin m → ℕ}
    {W : BlockMatrix n} (hW : W.PosSemidef) (hdiag : IsBlockDiagonal n W) :
    (blockMultiplier n (blockTrace n W) - W).PosSemidef := by
  let A := fun i => (blockTrace n W i) • (1 : Matrix (Fin (n i)) (Fin (n i)) ℂ) -
    W.submatrix (Sigma.mk i) (Sigma.mk i)
  have hA : ∀ i, (A i).PosSemidef := blockTrace_smul_one_sub_posSemidef hW
  have heq : Matrix.blockDiagonal' A = blockMultiplier n (blockTrace n W) - W := by
    ext ⟨i, a⟩ ⟨j, b⟩
    obtain rfl | hij := eq_or_ne i j
    · simp [A, blockMultiplier, Matrix.diagonal_apply, Matrix.one_apply]
    · have hzero := (isBlockDiagonal_iff n W).mp hdiag ⟨i, a⟩ ⟨j, b⟩ hij
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hij, blockMultiplier, hij, hzero]
  rw [← heq]
  exact posSemidef_blockDiagonal A hA

end SchurEntropy
