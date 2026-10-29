import SchurEntropy.PhaseCovariant.NormalForm

/-! # Density-state and full-matrix formulations of covariance

For a quantum channel, testing covariance on density matrices suffices: the
compared maps preserve Hermitian matrices, and density matrices determine such
complex-linear maps. Thus the paper's state-only formulation has exactly the
same content as the full-matrix definition used for the normal form.
-/

noncomputable section
open scoped Matrix

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Covariance can be extended from density matrices to every complex matrix. -/
theorem covariance_of_mstate (Φ : CPTPMap d d) (U : Matrix d d ℂ)
    (h : ∀ ρ : MState d,
      Φ.map (U * ρ.m * Uᴴ) = U * Φ.map ρ.m * Uᴴ) :
    ∀ X : Matrix d d ℂ, Φ.map (U * X * Uᴴ) = U * Φ.map X * Uᴴ := by
  let L : HPMap d d ℂ := {
    toLinearMap := Φ.map ∘ₗ MatrixMap.conj U
    HP := (MatrixMap.conj_isPositive U).IsHermitianPreserving.comp Φ.HP }
  let R : HPMap d d ℂ := {
    toLinearMap := MatrixMap.conj U ∘ₗ Φ.map
    HP := Φ.HP.comp (MatrixMap.conj_isPositive U).IsHermitianPreserving }
  have heq : L = R := HPMap.funext_mstate h
  intro X
  exact congrArg (fun F : HPMap d d ℂ => F.map X) heq

/-- Fixed-basis phase covariance tested only on density matrices. -/
def PhaseCovariantOnStates (Φ : CPTPMap d d) : Prop :=
  ∀ (z : d → ℂ), (∀ i, ‖z i‖ = 1) → ∀ ρ : MState d,
    Φ.map (Matrix.diagonal z * ρ.m * (Matrix.diagonal z)ᴴ) =
      Matrix.diagonal z * Φ.map ρ.m * (Matrix.diagonal z)ᴴ

/-- State-only angle covariance, exactly with the paper's real-angle quantifier. -/
def PhaseCovariantAnglesOnStates (Φ : CPTPMap d d) : Prop :=
  ∀ (θ : d → ℝ), ∀ ρ : MState d,
    Φ.map (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) * ρ.m *
      (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)))ᴴ) =
      Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)) * Φ.map ρ.m *
        (Matrix.diagonal (fun i => Complex.exp ((θ i : ℂ) * Complex.I)))ᴴ

/-- Density-state covariance is equivalent to full-matrix covariance. -/
theorem phaseCovariant_iff_onStates (Φ : CPTPMap d d) :
    PhaseCovariant Φ ↔ PhaseCovariantOnStates Φ := by
  constructor
  · intro h z hz ρ
    exact h z hz ρ.m
  · intro h z hz
    exact covariance_of_mstate Φ _ (h z hz)

/-- The full-matrix and state-only angle formulations are equivalent. -/
theorem phaseCovariantAngles_iff_onStates (Φ : CPTPMap d d) :
    PhaseCovariantAngles Φ ↔ PhaseCovariantAnglesOnStates Φ := by
  constructor
  · intro h θ ρ
    exact h θ ρ.m
  · intro h θ
    exact covariance_of_mstate Φ _ (h θ)

/-- The unit-phase definition is equivalent to the paper's state-only definition. -/
theorem phaseCovariant_iff_anglesOnStates (Φ : CPTPMap d d) :
    PhaseCovariant Φ ↔ PhaseCovariantAnglesOnStates Φ :=
  (phaseCovariant_iff_angles Φ).trans (phaseCovariantAngles_iff_onStates Φ)

/-- The same-basis normal form follows even from covariance tested only on states. -/
theorem phaseCovariantAnglesOnStates_iff_normalForm (Φ : CPTPMap d d) :
    PhaseCovariantAnglesOnStates Φ ↔ Nonempty (NormalForm Φ) := by
  rw [← phaseCovariant_iff_anglesOnStates, phaseCovariant_iff_normalForm]

end SchurEntropy.PhaseCovariant
