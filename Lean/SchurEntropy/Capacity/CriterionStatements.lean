import SchurEntropy.Capacity.Definitions
import SchurEntropy.Capacity.WeakReduction

noncomputable section
open scoped BigOperators

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {dA eA dB eB : Type*}
variable [Fintype dA] [DecidableEq dA] [Fintype eA] [DecidableEq eA]
variable [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]

/-- The trace expectation of the base-two spectral logarithm, extended by
zero on the kernel. For an optimal output center, the needed support
inclusion is proved separately rather than assumed in this definition. -/
def logExpectation (σ ρ : MState eA) : ℝ := logPairing σ ρ / Real.log 2

/-- The manuscript's weaker pure-input hypothesis. The first auxiliary
ensemble preserves only the output-center logarithmic expectation; the
second ensemble preserves its whole reduced input state. -/
def OutputCenterEntropicCriterion (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) : Prop :=
  ∀ ψ : Ket (dA × dB),
    ∃ (k l : ℕ) (E : MEnsemble dA (Fin k)) (F : MEnsemble dB (Fin l)),
      (∑ i, (E.distr i : ℝ) * logExpectation σ (Φ (E.states i))) =
        logExpectation σ (Φ (MState.pure ψ).traceRight) ∧
      Ensemble.mix F = (MState.pure ψ).traceLeft ∧
      meanOutputEntropy Φ E + meanOutputEntropy Ω F ≤
        stateEntropy ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ))

theorem mean_logExpectation_eq (Φ : CPTPMap dA eA) (σ : MState eA)
    {k : ℕ} (E : MEnsemble dA (Fin k)) :
    (∑ i, (E.distr i : ℝ) * logExpectation σ (Φ (E.states i))) =
      meanLogPairing Φ σ E / Real.log 2 := by
  simp only [logExpectation, meanLogPairing, Finset.sum_div, mul_div_assoc]

theorem outputCenterEntropicCriterion_iff_nat (Φ : CPTPMap dA eA)
    (Ω : CPTPMap dB eB) (σ : MState eA) :
    OutputCenterEntropicCriterion Φ Ω σ ↔ WeakPureInputBound Φ Ω σ := by
  constructor <;> intro h ψ <;> obtain ⟨k, l, E, F, hE, hF, hs⟩ := h ψ
  · refine ⟨k, l, E, F, ?_, hF, ?_⟩
    · rw [mean_logExpectation_eq, logExpectation] at hE
      exact (div_left_inj' log_two_pos.ne').mp hE
    · rw [meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
        meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
        stateEntropy_eq_vonNeumann_div_log_two, ← add_div] at hs
      exact (div_le_div_iff_of_pos_right log_two_pos).mp hs
  · refine ⟨k, l, E, F, ?_, hF, ?_⟩
    · rw [mean_logExpectation_eq, logExpectation, hE]
    · rw [meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
        meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
        stateEntropy_eq_vonNeumann_div_log_two, ← add_div]
      exact (div_le_div_iff_of_pos_right log_two_pos).mpr hs

/-- Preserving the full first marginal implies preserving its output-center
expectation, for any center. No support or optimality premise is needed. -/
theorem standard_implies_outputCenter (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) (h : StandardEntropicCriterion Φ Ω) :
    OutputCenterEntropicCriterion Φ Ω σ := by
  intro ψ
  obtain ⟨k, l, E, F, hE, hF, hs⟩ := h ψ
  refine ⟨k, l, E, F, ?_, hF, hs⟩
  rw [mean_logExpectation_eq, meanLogPairing_eq_mix, hE]
  rfl

end SchurEntropy.Capacity
