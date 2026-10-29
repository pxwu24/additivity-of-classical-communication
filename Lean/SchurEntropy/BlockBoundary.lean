import SchurEntropy.EntropyContinuity
import Mathlib.Tactic.FunProp

noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator

namespace SchurEntropy

variable {X : Type*} [TopologicalSpace X]

/-- Entropy is continuous along every continuous Hermitian matrix family. -/
theorem continuous_entropy_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : X → Matrix ι ι ℂ) (hA : Continuous A) (hHerm : ∀ x, (A x).IsHermitian) :
    Continuous (fun x => entropy (A x)) :=
  continuousOn_entropy.comp_continuous hA hHerm

theorem continuous_blockTrace_family {m : ℕ} (n : Fin m → ℕ)
    (A : X → BlockMatrix n) (hA : Continuous A) :
    Continuous (fun x => blockTrace n (A x)) := by
  unfold blockTrace
  fun_prop

theorem continuous_blockSchur_family {m : ℕ} {n : Fin m → ℕ}
    (C : X → Matrix (Fin m) (Fin m) ℂ) (H : X → BlockMatrix n)
    (hC : Continuous C) (hH : Continuous H) :
    Continuous (fun x => blockSchur (C x) (H x)) := by
  unfold blockSchur Matrix.hadamard Matrix.submatrix
  fun_prop

theorem continuous_pinching_family {m : ℕ} (n : Fin m → ℕ)
    (A : X → BlockMatrix n) (hA : Continuous A) :
    Continuous (fun x => pinching n (A x)) :=
  continuous_blockSchur_family (fun _ => 1) A continuous_const hA

theorem continuous_scalarSkeleton_family {m : ℕ}
    (C : X → Matrix (Fin m) (Fin m) ℂ) (r : X → Fin m → ℝ)
    (hC : Continuous C) (hr : Continuous r) :
    Continuous (fun x => scalarSkeleton (C x) (r x)) := by
  unfold scalarSkeleton scalarDiagonal
  fun_prop

/-- The scalar side of the inequality is continuous, including zero weights. -/
theorem continuous_scalarFunction_family {m : ℕ}
    (C : X → Matrix (Fin m) (Fin m) ℂ) (r y : X → Fin m → ℝ)
    (hC : Continuous C) (hr : Continuous r) (hy : Continuous y)
    (hCH : ∀ x, (C x).IsHermitian) :
    Continuous (fun x => scalarFunction (C x) (r x) (y x)) := by
  have hS := continuous_scalarSkeleton_family C r hC hr
  have hSH (x : X) : (scalarSkeleton (C x) (r x)).IsHermitian := by
    simpa only [scalarSkeleton, scalarDiagonal_conjTranspose] using
      isHermitian_mul_mul_conjTranspose
        (scalarDiagonal (fun i => Real.sqrt (r x i))) (hCH x)
  have hD : Continuous (fun x => scalarDiagonal (y x)) := by
    unfold scalarDiagonal
    fun_prop
  have hDH (x : X) : (scalarDiagonal (y x)).IsHermitian :=
    scalarDiagonal_conjTranspose (y x)
  have hP : Continuous (fun x => Matrix.diagonal (scalarSkeleton (C x) (r x)).diag) := by
    fun_prop
  have hPH (x : X) : (Matrix.diagonal (scalarSkeleton (C x) (r x)).diag).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr (fun i => (hSH x).apply i i)
  exact ((continuous_entropy_family _ (hS.add hD) (fun x => (hSH x).add (hDH x))).sub
    (continuous_entropy_family _ hP hPH)).sub (continuous_entropy_family _ hD hDH)

/-- The block entropy deficit is continuous along Hermitian matrix families. -/
theorem continuous_deficit_family {m : ℕ} (n : Fin m → ℕ)
    (J W : X → BlockMatrix n) (hJ : Continuous J) (hW : Continuous W)
    (hJH : ∀ x, (J x).IsHermitian) (hWH : ∀ x, (W x).IsHermitian) :
    Continuous (fun x => deficit n (J x) (W x)) := by
  have hPH (x : X) : (pinching n (J x)).IsHermitian :=
    ((Matrix.isHermitian_one.submatrix Sigma.fst).hadamard (hJH x))
  exact ((continuous_entropy_family _ (hJ.add hW) (fun x => (hJH x).add (hWH x))).sub
    (continuous_entropy_family _ (continuous_pinching_family n J hJ) hPH)).sub
      (continuous_entropy_family _ hW hWH)

@[simp] theorem pinching_one {m : ℕ} (n : Fin m → ℕ) :
    pinching n (1 : BlockMatrix n) = 1 := by
  ext a b
  by_cases h : a.1 = b.1
  · simp [pinching_apply, h]
  · have hab : a ≠ b := fun hab => h (congrArg Sigma.fst hab)
    simp [pinching_apply, h, hab]

theorem isBlockDiagonal_add_smul_one {m : ℕ} {n : Fin m → ℕ}
    {W : BlockMatrix n} (hW : IsBlockDiagonal n W) (t : ℝ) :
    IsBlockDiagonal n (W + t • 1) := by
  change pinching n (W + t • 1) = W + t • 1
  change blockSchur 1 (W + t • 1) = W + t • 1
  rw [blockSchur_add, blockSchur_smul]
  change pinching n W + t • pinching n 1 = W + t • 1
  rw [hW, pinching_one]

/-- It is enough to prove the inequality for strictly positive matrices:
positive identity perturbations preserve block diagonality, and both entropy
expressions are continuous at every positive semidefinite boundary point. -/
theorem blockEntropy_of_posDef {m : ℕ} (n : Fin m → ℕ)
    (hInterior : ∀ (C : Matrix (Fin m) (Fin m) ℂ) (H W : BlockMatrix n),
      C.PosDef → H.PosDef → W.PosDef → IsBlockDiagonal n W →
      scalarFunction C (blockTrace n H) (blockTrace n W) ≤
        deficit n (blockSchur C H) W)
    (C : Matrix (Fin m) (Fin m) ℂ) (H W : BlockMatrix n)
    (hC : C.PosSemidef) (hH : H.PosSemidef) (hW : W.PosSemidef)
    (hWD : IsBlockDiagonal n W) :
    scalarFunction C (blockTrace n H) (blockTrace n W) ≤
      deficit n (blockSchur C H) W := by
  let c : ℝ → Matrix (Fin m) (Fin m) ℂ := fun t => C + t • 1
  let h : ℝ → BlockMatrix n := fun t => H + t • 1
  let w : ℝ → BlockMatrix n := fun t => W + t • 1
  have hc : Continuous c := by unfold c; fun_prop
  have hh : Continuous h := by unfold h; fun_prop
  have hw : Continuous w := by unfold w; fun_prop
  have hcH (t : ℝ) : (c t).IsHermitian :=
    hC.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
  have hhH (t : ℝ) : (h t).IsHermitian :=
    hH.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
  have hwH (t : ℝ) : (w t).IsHermitian :=
    hW.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
  have hl := continuous_scalarFunction_family c
    (fun t => blockTrace n (h t)) (fun t => blockTrace n (w t)) hc
    (continuous_blockTrace_family n h hh) (continuous_blockTrace_family n w hw) hcH
  have hr := continuous_deficit_family n (fun t => blockSchur (c t) (h t)) w
    (continuous_blockSchur_family c h hc hh) hw
    (fun t => ((hcH t).submatrix Sigma.fst).hadamard (hhH t)) hwH
  have hleft : Tendsto (fun t => scalarFunction (c t) (blockTrace n (h t))
      (blockTrace n (w t))) (𝓝[>] 0)
      (𝓝 (scalarFunction C (blockTrace n H) (blockTrace n W))) := by
    simpa [c, h, w] using (hl.tendsto 0).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun t => deficit n (blockSchur (c t) (h t)) (w t))
      (𝓝[>] 0) (𝓝 (deficit n (blockSchur C H) W)) := by
    simpa [c, h, w] using (hr.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hInterior (c t) (h t) (w t)
    (Matrix.PosDef.posSemidef_add hC (Matrix.PosDef.one.smul (α := ℝ) ht))
    (Matrix.PosDef.posSemidef_add hH (Matrix.PosDef.one.smul (α := ℝ) ht))
    (Matrix.PosDef.posSemidef_add hW (Matrix.PosDef.one.smul (α := ℝ) ht))
    (isBlockDiagonal_add_smul_one hWD t)

end SchurEntropy
