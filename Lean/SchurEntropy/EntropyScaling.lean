import SchurEntropy.Definitions
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators ComplexOrder

namespace SchurEntropy

/-- Exact scaling of the matrix entropy function before taking the trace. -/
theorem negMulLog_cfc_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    cfc Real.negMulLog (t • A) =
      t • cfc Real.negMulLog A + Real.negMulLog t • A := by
  have hc : cfc (fun x : ℝ => Real.negMulLog (t * x)) A =
      cfc Real.negMulLog (t • A) :=
    cfc_comp_const_mul t Real.negMulLog A
      (hf := Real.continuous_negMulLog.continuousOn) (ha := hA)
  rw [← hc]
  have hf : (fun x : ℝ => Real.negMulLog (t * x)) =
      (fun x : ℝ => t * Real.negMulLog x + Real.negMulLog t * x) := by
    funext x
    rw [Real.negMulLog_mul]
    ring
  rw [hf]
  calc
    cfc (fun x : ℝ => t * Real.negMulLog x + Real.negMulLog t * x) A =
        cfc (fun x : ℝ => t * Real.negMulLog x) A +
          cfc (fun x : ℝ => Real.negMulLog t * x) A :=
      cfc_add A _ _
        (continuous_const.mul Real.continuous_negMulLog).continuousOn
        (continuous_const.mul continuous_id).continuousOn
    _ = t • cfc Real.negMulLog A + Real.negMulLog t • A :=
      congrArg₂ (fun X Y : Matrix ι ι ℂ => X + Y)
        (cfc_const_mul t Real.negMulLog A Real.continuous_negMulLog.continuousOn)
        (cfc_const_mul_id (Real.negMulLog t) A hA)

/-- Spectral entropy scales with the expected trace correction for
unnormalized positive matrices. The algebraic identity holds for all
Hermitian matrices under the total real logarithm convention. -/
theorem entropy_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (t • A) = t * entropy A +
      Real.negMulLog t * (Matrix.trace A).re / Real.log 2 := by
  unfold entropy
  rw [negMulLog_cfc_smul t hA]
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The trace correction cancels from the entropy deficit. -/
theorem deficit_smul {m : ℕ} (n : Fin m → ℕ) (t : ℝ)
    {J W : BlockMatrix n} (hJ : J.PosSemidef) (hW : W.PosSemidef) :
    deficit n (t • J) (t • W) = t * deficit n J W := by
  unfold deficit
  rw [← smul_add, show pinching n (t • J) = t • pinching n J from blockSchur_smul _ t J,
    entropy_smul t (hJ.add hW).isHermitian,
    entropy_smul t (pinching_posSemidef n hJ).isHermitian,
    entropy_smul t hW.isHermitian, trace_pinching, Matrix.trace_add, Complex.add_re]
  ring

end SchurEntropy
