import SchurEntropy
import Mathlib.Util.AssertNoSorry

/-! Reject any transitive axiom other than Lean's standard foundations for
every declaration in the imported `SchurEntropy` namespace. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`SchurEntropy).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      count := count + 1
  logInfo m!"Audited {count} SchurEntropy declarations: only standard foundational axioms."

#print axioms SchurEntropy.optimizedConcavity
#print axioms SchurEntropy.scalar_joint_convexity
#print axioms SchurEntropy.block_entropy_inequality
#print axioms SchurEntropy.Capacity.standard_entropic_criterion
#print axioms SchurEntropy.Capacity.output_center_entropic_criterion
#print axioms SchurEntropy.Capacity.output_center_criterion_of_optimal_ensemble
#print axioms SchurEntropy.Capacity.exists_optimalEnsemble
#print axioms SchurEntropy.Capacity.optimal_center_support

example : SchurEntropy.OptimizedConcavityStatement := SchurEntropy.optimizedConcavity
example : SchurEntropy.ScalarConvexityStatement := SchurEntropy.scalar_joint_convexity
example : SchurEntropy.BlockEntropyStatement := SchurEntropy.block_entropy_inequality

/-! Check the entropic criteria with their full ensemble hypotheses exposed. -/
section CapacityStatements
open QubitAdditivity SchurEntropy.Capacity
open scoped BigOperators

variable {d e f g : Type*}
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]
variable [Nonempty d] [Nonempty f]

example (Φ : CPTPMap d e) (Ω : CPTPMap f g)
    (h : ∀ ψ : Ket (d × f),
      ∃ (k l : ℕ) (E : MEnsemble d (Fin k)) (F : MEnsemble f (Fin l)),
        Ensemble.mix E = (MState.pure ψ).traceRight ∧
        Ensemble.mix F = (MState.pure ψ).traceLeft ∧
        meanOutputEntropy Φ E + meanOutputEntropy Ω F ≤
          stateEntropy ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ))) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  standard_entropic_criterion Φ Ω h

example (Φ : CPTPMap d e) (Ω : CPTPMap f g)
    (h : ∀ ψ : Ket (d × f),
      ∃ (k l : ℕ) (E : MEnsemble d (Fin k)) (F : MEnsemble f (Fin l)),
        (∑ i, (E.distr i : ℝ) * logExpectation (optimalOutputCenter Φ) (Φ (E.states i))) =
          logExpectation (optimalOutputCenter Φ) (Φ (MState.pure ψ).traceRight) ∧
        Ensemble.mix F = (MState.pure ψ).traceLeft ∧
        meanOutputEntropy Φ E + meanOutputEntropy Ω F ≤
          stateEntropy ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ))) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  output_center_entropic_criterion Φ Ω h

example (Φ : CPTPMap d e) (Ω : CPTPMap f g) {α : Type*} [Fintype α]
    (E : MEnsemble d α) (hE : holevoEnsembleValue Φ E = holevoInformation Φ)
    (h : OutputCenterEntropicCriterion Φ Ω (Φ (Ensemble.mix E))) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  output_center_criterion_of_optimal_ensemble Φ Ω E hE h

end CapacityStatements
