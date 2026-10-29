import SchurEntropy.Capacity.CenterSupport
import SchurEntropy.Capacity.OutputCenterMixture
import SchurEntropy.Capacity.Gibbs

/-! The relative-entropy radius inequality for an actual optimal output
ensemble, including singular centers. Optimality gives a uniform lower bound
on regularized log pairings. Spectral regularization proves support and the
limit, rather than postulating a radius condition for the center. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace SchurEntropy.Capacity
open QubitAdditivity QubitAdditivity.BetaEntropy

variable {d e α : Type*} [Fintype d] [DecidableEq d]
  [Fintype e] [DecidableEq e] [Fintype α]

/-- Optimality bounds every regularized logarithmic pairing from below. -/
theorem optimal_center_regularizedPairing_lower (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d)
    {t : ℝ} (ht : 0 < t) :
    -holevo Φ - Sᵥₙ (Φ ρ) ≤ regularizedLogPairing (Φ (Ensemble.mix E)) (Φ ρ) t := by
  have hlo := optimal_center_entropy_increment_lower_simple Φ E hE ρ ht
  have hup := psi_state_increment_le_regularized (Φ (Ensemble.mix E)) (Φ ρ) ht
  have h := le_of_mul_le_mul_left (hlo.trans hup) ht
  linarith

/-- The logarithmic pairing has a finite limit at any optimal center, even
when the center is singular. -/
theorem optimal_center_logPairing_limit (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d) :
    Tendsto (regularizedLogPairing (Φ (Ensemble.mix E)) (Φ ρ)) (𝓝[>] 0)
      (𝓝 (logPairing (Φ (Ensemble.mix E)) (Φ ρ))) := by
  apply regularizedLogPairing_tendsto_of_bddBelow
  refine ⟨-holevo Φ - Sᵥₙ (Φ ρ), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact optimal_center_regularizedPairing_lower Φ E hE ρ ht

/-- No channel output has spectral weight on the kernel of an optimal
output center. -/
theorem optimal_center_kernel_weight_zero (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d)
    (i : e) (hi : (Φ (Ensemble.mix E)).M.H.eigenvalues i = 0) :
    (BetaLogKM.coordinates (Φ (Ensemble.mix E)).M.H (Φ ρ).m i i).re = 0 := by
  apply kernel_weight_zero_of_regularized_bddBelow (Φ (Ensemble.mix E)) (Φ ρ) ?_ i hi
  refine ⟨-holevo Φ - Sᵥₙ (Φ ρ), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact optimal_center_regularizedPairing_lower Φ E hE ρ ht

/-- Every channel output is supported on the support of an optimal center. -/
theorem optimal_center_support (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d) :
    (Φ ρ).M.support ≤ (Φ (Ensemble.mix E)).M.support := by
  apply support_le_of_regularized_bddBelow
  refine ⟨-holevo Φ - Sᵥₙ (Φ ρ), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact optimal_center_regularizedPairing_lower Φ E hE ρ ht

/-- Every output lies within the Holevo relative-entropy radius of an
actual optimal output center. Entropies and logarithms are in nats. -/
theorem optimal_center_radius (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d) :
    -Sᵥₙ (Φ ρ) - logPairing (Φ (Ensemble.mix E)) (Φ ρ) ≤ holevo Φ := by
  have hbound : -holevo Φ - Sᵥₙ (Φ ρ) ≤ logPairing (Φ (Ensemble.mix E)) (Φ ρ) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (optimal_center_logPairing_limit Φ E hE ρ)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact optimal_center_regularizedPairing_lower Φ E hE ρ ht
  linarith

/-- Gibbs' entropy bound at an actual optimal output center, justified also
on the boundary by the regularized pairing limit. -/
theorem optimal_center_gibbs (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d) :
    Sᵥₙ (Φ ρ) + logPairing (Φ (Ensemble.mix E)) (Φ ρ) ≤ 0 := by
  exact Gibbs.gibbs_of_regularized_limit (Φ (Ensemble.mix E)) (Φ ρ)
    (optimal_center_logPairing_limit Φ E hE ρ)

end SchurEntropy.Capacity
