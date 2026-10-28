import SchurEntropy.Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SchurEntropy

/-- Operator monotonicity of the spectral logarithm, in PSD-difference form. -/
theorem logarithm_sub_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hAB : (B - A).PosSemidef) :
    (cfc Real.log B - cfc Real.log A).PosSemidef := by
  have hle : A ≤ B := sub_nonneg.mp hAB.nonneg
  have hl := CFC.log_le_log hle hA.isStrictlyPositive
  change cfc Real.log A ≤ cfc Real.log B at hl
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hl)

end SchurEntropy
