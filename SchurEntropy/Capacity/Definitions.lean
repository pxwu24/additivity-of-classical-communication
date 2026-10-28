import SchurEntropy.Definitions
import QubitAdditivity.UpperBound

/-!
# Channels, ensembles, and Holevo information in bits

The channel and ensemble types are the concrete finite-dimensional CPTP maps,
density matrices, and probability distributions from the pinned dependency.
The bit-valued entropy below is exactly the spectral entropy already used by
the block-entropy results. Holevo information is the supremum over all finite
ensembles of genuine states; a bridge to that supremum is proved below.
-/

noncomputable section
open scoped BigOperators

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {d e f g α : Type*}
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]
variable [Fintype α]

/-- The spectral von Neumann entropy of a density matrix, in bits. -/
def stateEntropy (ρ : MState d) : ℝ := SchurEntropy.entropy ρ.m

/-- The average of the output entropies for a finite input ensemble. -/
def meanOutputEntropy (Φ : CPTPMap d e) (E : MEnsemble d α) : ℝ :=
  ∑ i, (E.distr i : ℝ) * stateEntropy (Φ (E.states i))

/-- The finite-ensemble Holevo expression, in bits. -/
def holevoEnsembleValue (Φ : CPTPMap d e) (E : MEnsemble d α) : ℝ :=
  stateEntropy (Φ (Ensemble.mix E)) - meanOutputEntropy Φ E

/-- Holevo information in bits. The equality to the corresponding ensemble
supremum is proved by `holevoInformation_eq_sSup`. -/
def holevoInformation (Φ : CPTPMap d e) : ℝ :=
  QubitAdditivity.holevo Φ / Real.log 2

/-- Every value of the Holevo expression over a finite ensemble. -/
def holevoEnsembleValues (Φ : CPTPMap d e) : Set ℝ :=
  {v | ∃ k : ℕ, ∃ E : MEnsemble d (Fin k), holevoEnsembleValue Φ E = v}

/-- An optimal ensemble means actual attainment of the finite-ensemble
Holevo supremum. No relative-entropy or radius bound is built into this definition. -/
def OptimalEnsemble (Φ : CPTPMap d e) (E : MEnsemble d α) : Prop :=
  holevoEnsembleValue Φ E = holevoInformation Φ

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem stateEntropy_eq_vonNeumann_div_log_two (ρ : MState d) :
    stateEntropy ρ = Sᵥₙ ρ / Real.log 2 := by
  rw [entropy_eq_openai]
  rfl

theorem meanOutputEntropy_eq_avgOutputEntropy_div_log_two
    (Φ : CPTPMap d e) (E : MEnsemble d α) :
    meanOutputEntropy Φ E = QubitAdditivity.avgOutputEntropy Φ E / Real.log 2 := by
  simp only [meanOutputEntropy, stateEntropy_eq_vonNeumann_div_log_two,
    QubitAdditivity.avgOutputEntropy, Finset.sum_div, mul_div_assoc]

theorem holevoEnsembleValue_eq_holevoValue_div_log_two
    (Φ : CPTPMap d e) (E : MEnsemble d α) :
    holevoEnsembleValue Φ E = QubitAdditivity.holevoValue Φ E / Real.log 2 := by
  rw [holevoEnsembleValue, stateEntropy_eq_vonNeumann_div_log_two,
    meanOutputEntropy_eq_avgOutputEntropy_div_log_two, ← sub_div]
  rfl

theorem optimalEnsemble_iff_nat (Φ : CPTPMap d e) (E : MEnsemble d α) :
    OptimalEnsemble Φ E ↔ QubitAdditivity.holevoValue Φ E = QubitAdditivity.holevo Φ := by
  unfold OptimalEnsemble holevoInformation
  rw [holevoEnsembleValue_eq_holevoValue_div_log_two]
  exact div_left_inj' log_two_pos.ne'

theorem holevoEnsembleValue_le_holevoInformation
    (Φ : CPTPMap d e) (E : MEnsemble d α) :
    holevoEnsembleValue Φ E ≤ holevoInformation Φ := by
  have h := QubitAdditivity.holevoValue_le_holevo Φ
    (Ensemble.congrMEnsemble (Fintype.equivFin α) E)
  rw [QubitAdditivity.holevoValue_reindex] at h
  rw [holevoEnsembleValue_eq_holevoValue_div_log_two, holevoInformation]
  exact div_le_div_of_nonneg_right h log_two_pos.le

theorem holevoEnsembleValues_bddAbove (Φ : CPTPMap d e) :
    BddAbove (holevoEnsembleValues Φ) := by
  refine ⟨holevoInformation Φ, ?_⟩
  rintro v ⟨k, E, rfl⟩
  exact holevoEnsembleValue_le_holevoInformation Φ E

theorem holevoEnsembleValues_nonempty [Nonempty d] (Φ : CPTPMap d e) :
    (holevoEnsembleValues Φ).Nonempty := by
  obtain ⟨v, k, E, rfl⟩ := QubitAdditivity.holevoValues_nonempty Φ
  exact ⟨holevoEnsembleValue Φ E, k, E, rfl⟩

/-- The advertised bit-valued Holevo quantity is exactly the supremum of the
actual finite-ensemble entropy expressions. -/
theorem holevoInformation_eq_sSup [Nonempty d] (Φ : CPTPMap d e) :
    holevoInformation Φ = sSup (holevoEnsembleValues Φ) := by
  apply le_antisymm
  · rw [holevoInformation, div_le_iff₀ log_two_pos]
    apply csSup_le (QubitAdditivity.holevoValues_nonempty Φ)
    rintro v ⟨k, E, rfl⟩
    have h := le_csSup (holevoEnsembleValues_bddAbove Φ)
      (show holevoEnsembleValue Φ E ∈ holevoEnsembleValues Φ from ⟨k, E, rfl⟩)
    rw [holevoEnsembleValue_eq_holevoValue_div_log_two] at h
    exact (div_le_iff₀ log_two_pos).mp h
  · exact csSup_le (holevoEnsembleValues_nonempty Φ) fun v hv => by
      rcases hv with ⟨k, E, rfl⟩
      exact holevoEnsembleValue_le_holevoInformation Φ E

/-- Product ensembles always give the lower bound for additivity. -/
theorem holevoInformation_product_ge [Nonempty d] [Nonempty f]
    (Φ : CPTPMap d e) (Ω : CPTPMap f g) :
    holevoInformation Φ + holevoInformation Ω ≤ holevoInformation (Φ ⊗ᶜᵖ Ω) := by
  simpa only [holevoInformation, add_div] using
    div_le_div_of_nonneg_right (QubitAdditivity.holevo_product_ge Φ Ω) log_two_pos.le

/-- The standard entropic criterion: auxiliary finite ensembles preserve both
reduced input states and their mean output entropies are bounded by the joint
output entropy for every pure input. -/
def StandardEntropicCriterion (Φ : CPTPMap d e) (Ω : CPTPMap f g) : Prop :=
  ∀ ψ : Ket (d × f),
    ∃ (k l : ℕ) (E : MEnsemble d (Fin k)) (F : MEnsemble f (Fin l)),
      Ensemble.mix E = (MState.pure ψ).traceRight ∧
      Ensemble.mix F = (MState.pure ψ).traceLeft ∧
      meanOutputEntropy Φ E + meanOutputEntropy Ω F ≤
        stateEntropy ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ))

end SchurEntropy.Capacity
