/-
Adapted from KitaKen1/qubit-strong-additivity,
commit 90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/BetaIsometryEntropy.lean.
Apache-2.0; see third_party/Apache-2.0.txt and third_party/NOTICE.
Changes: narrowed imports, renamed namespace, and used entropy in bits.
-/
import SchurEntropy.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Tactic.FunProp

noncomputable section
open Matrix

namespace SchurEntropy

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Rectangular isometric conjugation preserves the nonunital star algebra structure. -/
def isometryHom (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1) :
    Matrix ι ι ℂ →⋆ₙₐ[ℝ] Matrix κ κ ℂ where
  toFun A := V * A * Vᴴ
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  map_mul' A B := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V (B * Vᴴ), hV, Matrix.one_mul]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul]
  map_star' A := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- Functional calculus for a continuous zero-preserving function commutes with an isometry. -/
theorem cfc_isometry (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    cfc f (V * A * Vᴴ) = V * cfc f A * Vᴴ := by
  have hm := (isometryHom V hV).map_cfcₙ f A hf.continuousOn hf0
    (by change Continuous (fun X : Matrix ι ι ℂ => V * X * Vᴴ); fun_prop) hA
    (Matrix.isHermitian_mul_mul_conjTranspose V hA)
  rw [cfcₙ_eq_cfc hf.continuousOn hf0, cfcₙ_eq_cfc hf.continuousOn hf0] at hm
  exact hm.symm

omit [DecidableEq κ] in
/-- Rectangular isometric conjugation preserves trace without a trace-one assumption. -/
theorem trace_isometry (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix ι ι ℂ) : Matrix.trace (V * A * Vᴴ) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- Rectangular isometric conjugation preserves the unnormalized entropy in bits. -/
theorem entropy_isometry (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    entropy (V * A * Vᴴ) = entropy A := by
  unfold entropy
  rw [cfc_isometry V hV A hA Real.negMulLog Real.continuous_negMulLog (by simp),
    trace_isometry V hV]

end SchurEntropy
