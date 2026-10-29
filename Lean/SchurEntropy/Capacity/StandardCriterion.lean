import SchurEntropy.Capacity.Definitions
import QubitAdditivity.UpperBound

/-!
# The standard entropic criterion for Holevo additivity

This is the finite-ensemble criterion preserving both reduced input states.
The proof uses the genuine finite-ensemble and spectral-decomposition argument
in the pinned `QubitAdditivity.UpperBound` dependency, converting its natural-log
entropy to the repository's spectral entropy in bits.
-/

noncomputable section
open scoped BigOperators

namespace SchurEntropy.Capacity

open QubitAdditivity

variable {dA eA dB eB : Type*}
variable [Fintype dA] [Fintype eA] [Fintype dB] [Fintype eB]
variable [DecidableEq dA] [DecidableEq eA] [DecidableEq dB] [DecidableEq eB]

/-- The manuscript's bit-entropy hypothesis is exactly the explicit
pure-input criterion in the natural-log channel library. -/
theorem standardEntropicCriterion_iff_pureInputBound
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) :
    StandardEntropicCriterion Φ Ω ↔ PureInputBound Φ Ω := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h ψ
    obtain ⟨k, l, E, F, hE, hF, hS⟩ := h ψ
    refine ⟨k, l, E, F, hE, hF, ?_⟩
    rw [meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
      meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
      stateEntropy_eq_vonNeumann_div_log_two, ← add_div] at hS
    exact (div_le_div_iff_of_pos_right hlog).mp hS
  · intro h ψ
    obtain ⟨k, l, E, F, hE, hF, hS⟩ := h ψ
    refine ⟨k, l, E, F, hE, hF, ?_⟩
    rw [meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
      meanOutputEntropy_eq_avgOutputEntropy_div_log_two,
      stateEntropy_eq_vonNeumann_div_log_two, ← add_div]
    exact (div_le_div_iff_of_pos_right hlog).mpr hS

/-- The standard entropic criterion implies Holevo additivity for arbitrary
finite-dimensional channels. The only analytic hypothesis is the stated
pure-input ensemble bound with both marginal compatibility conditions. -/
theorem standard_entropic_criterion [Nonempty dA] [Nonempty dB]
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (h : StandardEntropicCriterion Φ Ω) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  have hnat := holevo_prod_eq_of_pureInputBound Φ Ω
    ((standardEntropicCriterion_iff_pureInputBound Φ Ω).mp h)
  unfold holevoInformation
  rw [hnat, add_div]

end SchurEntropy.Capacity
