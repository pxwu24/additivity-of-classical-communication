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
#print axioms SchurEntropy.Qubit.single_coherent_qubit_output_additivity
#print axioms SchurEntropy.Qubit.all_qubit_channels_additivity
#print axioms SchurEntropy.Qubit.exists_qubit_output_decomposition_general

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

/-! Result 2 with the actual channel representation and completeness exposed. -/
section QubitStatements
open Matrix QubitAdditivity SchurEntropy.Capacity SchurEntropy.Qubit
open scoped Matrix BigOperators MatrixMap ComplexOrder

variable {D dB eB : Type*}
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype dB] [DecidableEq dB] [Nonempty dB]
variable [Fintype eB] [DecidableEq eB]

example (Φ : CPTPMap D (Fin 2)) (Ω : CPTPMap dB eB)
    (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (a c : D → ℂ) (E₀ E₁ : Matrix D D ℂ)
    (h₀ : E₀.PosSemidef) (h₁ : E₁.PosSemidef)
    (hcomplete : vecMulVec a (star a) + vecMulVec c (star c) + E₀ + E₁ = 1)
    (hact : ∀ X : Matrix D D ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
        QubitOutputForm.rows a c * X * (QubitOutputForm.rows a c)ᴴ +
          Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace)) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  single_coherent_qubit_output_additivity Φ Ω U a c E₀ E₁ h₀ h₁ hcomplete hact

example (Φ : CPTPMap (Fin 2) (Fin 2)) (Ω : CPTPMap dB eB) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω :=
  all_qubit_channels_additivity Φ Ω

example (Φ : CPTPMap D (Fin 2)) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
    ∃ a b : Fin (Fintype.card D - 1) → D → ℂ, ∃ E₀ E₁ : Matrix D D ℂ,
      E₀.PosSemidef ∧ E₁.PosSemidef ∧
      (∑ j, (vecMulVec (a j) (star (a j)) + vecMulVec (b j) (star (b j)))) +
        E₀ + E₁ = 1 ∧
      ∀ X : Matrix D D ℂ,
        (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
          (∑ j, QubitOutputForm.rows (a j) (b j) * X *
            (QubitOutputForm.rows (a j) (b j))ᴴ) +
          Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace) :=
  exists_qubit_output_decomposition_general Φ

end QubitStatements
