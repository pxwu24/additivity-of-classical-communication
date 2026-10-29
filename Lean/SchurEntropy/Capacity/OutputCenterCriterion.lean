import SchurEntropy.Capacity.CriterionStatements
import SchurEntropy.Capacity.OptimalOutputCenter
import SchurEntropy.Capacity.OutputCenterRadius

/-!
# The weaker output-center criterion for Holevo additivity

Both entropy bounds at the center are derived from actual finite-ensemble
optimality, including when the center is singular. The exported theorem for
the chosen optimal output center has only the manuscript's entropic hypothesis.
-/

noncomputable section

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {dA eA dB eB α : Type*}
variable [Fintype dA] [DecidableEq dA] [Fintype eA] [DecidableEq eA]
variable [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]
variable [Nonempty dA] [Nonempty dB] [Fintype α]

/-- The weaker criterion for the average output of any genuinely optimal
ensemble. Optimality is the original Holevo supremum equality. -/
theorem output_center_criterion_of_optimal_ensemble
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (E : MEnsemble dA α)
    (hE : OptimalEnsemble Φ E)
    (h : OutputCenterEntropicCriterion Φ Ω (Φ (Ensemble.mix E))) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  have hEnat := (optimalEnsemble_iff_nat Φ E).mp hE
  have heq := holevo_prod_eq_of_weak_and_center_bounds Φ Ω (Φ (Ensemble.mix E))
    ((outputCenterEntropicCriterion_iff_nat Φ Ω _).mp h)
    (fun ρ => optimal_center_gibbs Φ E hEnat ρ)
    (fun ρ => optimal_center_radius Φ E hEnat ρ)
  unfold holevoInformation
  rw [heq, add_div]

/-- The manuscript's weaker entropic criterion. The center is constructed
from the proved existence of an attaining ensemble; there is no additional
radius, support, full-rank, or existence hypothesis. -/
theorem output_center_entropic_criterion
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (h : OutputCenterEntropicCriterion Φ Ω (optimalOutputCenter Φ)) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  output_center_criterion_of_optimal_ensemble Φ Ω (chosenOptimalEnsemble Φ)
    (chosenOptimalEnsemble_optimal Φ) h

end SchurEntropy.Capacity
