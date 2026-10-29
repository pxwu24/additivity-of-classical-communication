import SchurEntropy.Capacity.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Fixed-basis phase covariance and its matrix normal form

Covariance is defined independently of the normal form, using every diagonal
unitary in the fixed matrix basis. A normal form records its actual action on
all complex matrices, together with complete-positivity and normalization data.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Covariance under all diagonal unitaries in the fixed standard basis. -/
def PhaseCovariant (Φ : CPTPMap d d) : Prop :=
  ∀ (z : d → ℂ), (∀ i, ‖z i‖ = 1) → ∀ X : Matrix d d ℂ,
    Φ.map (Matrix.diagonal z * X * (Matrix.diagonal z)ᴴ) =
      Matrix.diagonal z * Φ.map X * (Matrix.diagonal z)ᴴ

/-- The equivalent angle-parametrized covariance appearing in the paper. -/
def PhaseCovariantAngles (Φ : CPTPMap d d) : Prop :=
  ∀ (θ : d → ℝ), ∀ X : Matrix d d ℂ,
    Φ.map (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) * X *
      (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)))ᴴ) =
      Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) * Φ.map X *
        (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)))ᴴ

/-- Every diagonal unitary is obtained from real angles in the same basis. -/
theorem phaseCovariant_iff_angles (Φ : CPTPMap d d) :
    PhaseCovariant Φ ↔ PhaseCovariantAngles Φ := by
  constructor
  · intro h θ X
    exact h _ (fun i => Complex.norm_exp_ofReal_mul_I (θ i)) X
  · intro h z hz X
    have heq : (fun i => Complex.exp (((Complex.arg (z i)) : ℂ) * Complex.I)) = z := by
      funext i
      simpa [hz i] using Complex.norm_mul_exp_arg_mul_I (z i)
    simpa only [heq] using h (fun i => Complex.arg (z i)) X

/-- The Schur-plus-classical normal form in that same fixed basis. -/
structure NormalForm (Φ : CPTPMap d d) where
  C : Matrix d d ℂ
  p : Matrix d d ℝ
  C_psd : C.PosSemidef
  p_nonneg : ∀ i j, 0 ≤ p i j
  p_colsum : ∀ j, ∑ i, p i j = 1
  C_diag : ∀ i, C i i = (p i i : ℂ)
  action : ∀ X : Matrix d d ℂ,
    Φ.map X = C.hadamard X + Matrix.diagonal
      (fun i => ∑ j, if i ≠ j then (p i j : ℂ) * X j j else 0)

end SchurEntropy.PhaseCovariant
