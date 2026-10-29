import SchurEntropy.PhaseCovariant.NormalForm
import SchurEntropy.PhaseCovariant.CovarianceOnStates
import SchurEntropy.PhaseCovariant.UnitaryInvariance
import SchurEntropy.PhaseCovariant.OptimalCenter
import SchurEntropy.PhaseCovariant.EntropyBound
import SchurEntropy.PhaseCovariant.LogCompatibility
import SchurEntropy.Capacity.OutputCenterCriterion

/-!
# Strong Holevo additivity for every fixed-basis phase-covariant channel

The channel hypothesis is covariance under all diagonal unitaries, independently
of the proved normal form. The conclusion is equality of the actual finite-
ensemble Holevo information in bits for every finite-dimensional partner.
-/

noncomputable section
open Matrix QubitAdditivity
open scoped BigOperators ComplexOrder MatrixMap

namespace SchurEntropy.PhaseCovariant
open SchurEntropy.Capacity

variable {d f g : Type*}
variable [Fintype d] [DecidableEq d] [Nonempty d]
variable [Fintype f] [DecidableEq f] [Nonempty f]
variable [Fintype g] [DecidableEq g]

omit [Nonempty d] in
/-- The explicit comparison input and partner branches satisfy the weaker
entropic criterion at any diagonal center, including singular centers. -/
theorem NormalForm.weakPureInputBound {Φ : CPTPMap d d} (N : NormalForm Φ)
    (Ω : CPTPMap f g) (σ : MState d)
    (hσ : σ.m = Matrix.diagonal σ.m.diag) : WeakPureInputBound Φ Ω σ := by
  intro ψ
  let ρ := comparisonState (MState.pure ψ).traceRight
  let E : MEnsemble d (Fin 2) := pairEnsemble 1 ρ ρ
  have hE : Ensemble.mix E = ρ := by
    apply MState.ext_m
    change (Ensemble.mix (pairEnsemble 1 ρ ρ)).m = ρ.m
    rw [pairEnsemble_mix_m]
    simp
  refine ⟨2, Fintype.card d, E,
    Ensemble.congrMEnsemble (Fintype.equivFin d) (branchEnsemble ψ), ?_, ?_, ?_⟩
  · rw [meanLogPairing_eq_mix, hE]
    exact N.comparisonState_logPairing σ _ hσ
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    exact branchEnsemble_mix ψ
  · simpa [E, avgOutputEntropy_pair, avgOutputEntropy_reindex, ρ] using
      N.pure_entropy_bound Ω ψ

/-- Main result 1 for a channel in the proved Schur-plus-classical normal form. -/
theorem normal_form_additivity (Φ : CPTPMap d d) (Ω : CPTPMap f g)
    (N : NormalForm Φ) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  obtain ⟨k, E, hE, hdiag⟩ := exists_diagonal_optimal_ensemble Φ (N.phaseCovariant Φ)
  apply output_center_criterion_of_optimal_ensemble Φ Ω E hE
  apply (outputCenterEntropicCriterion_iff_nat Φ Ω _).mpr
  exact N.weakPureInputBound Ω _ hdiag

/-- Main result 1. Independent phases refer to one fixed matrix basis; no
normal-form data, entropy inequality, or center assumption is required. -/
theorem phase_covariant_additivity (Φ : CPTPMap d d) (Ω : CPTPMap f g)
    (hΦ : PhaseCovariant Φ) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  normal_form_additivity Φ Ω (normalFormOfPhaseCovariant Φ hΦ)

/-- The same theorem with the manuscript's exact real-phase parametrization. -/
theorem phase_covariant_angles_additivity (Φ : CPTPMap d d) (Ω : CPTPMap f g)
    (hΦ : PhaseCovariantAngles Φ) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  phase_covariant_additivity Φ Ω ((phaseCovariant_iff_angles Φ).mpr hΦ)

/-- The phase-covariance hypothesis may be checked only on density matrices. -/
theorem phase_covariant_states_additivity (Φ : CPTPMap d d) (Ω : CPTPMap f g)
    (hΦ : PhaseCovariantAnglesOnStates Φ) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  phase_covariant_additivity Φ Ω ((phaseCovariant_iff_anglesOnStates Φ).mpr hΦ)

/-- Covariance in any specified fixed orthonormal basis suffices. `U` gives
the basis vectors in the original coordinates. -/
theorem phase_covariant_in_basis_additivity (Φ : CPTPMap d d) (Ω : CPTPMap f g)
    (U : Matrix.unitaryGroup d ℂ)
    (hΦ : PhaseCovariantAnglesOnStates
      (CPTPMap.ofUnitary (star U) ∘ₘ Φ ∘ₘ CPTPMap.ofUnitary U)) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  have hadd := phase_covariant_states_additivity _ Ω hΦ
  simpa only [holevoInformation_unitary_coordinates,
    holevoInformation_prod_unitary_coordinates] using hadd

end SchurEntropy.PhaseCovariant
