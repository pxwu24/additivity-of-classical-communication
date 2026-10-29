import SchurEntropy.Capacity.Definitions
import QubitAdditivity.RotationInvariant

/-! Holevo information is independent of a fixed unitary change of coordinates,
including when the channel is tensored with an arbitrary partner. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder MatrixMap

namespace SchurEntropy.PhaseCovariant
open QubitAdditivity SchurEntropy.Capacity QubitAdditivity.RotationInvariant

@[reducible] local instance invarianceMatrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {d e f g : Type*}
  [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
  [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]

/-- Inverse unitary preprocessing is itself a channel. -/
theorem ofUnitary_comp_star (U : Matrix.unitaryGroup d ℂ) :
    CPTPMap.ofUnitary U ∘ₘ CPTPMap.ofUnitary (star U) = CPTPMap.id := by
  apply CPTPMap.ext
  apply LinearMap.ext
  intro X
  change (U : Matrix d d ℂ) * ((U : Matrix d d ℂ)ᴴ * X *
    ((U : Matrix d d ℂ)ᴴ)ᴴ) * (U : Matrix d d ℂ)ᴴ = X
  rw [Matrix.conjTranspose_conjTranspose]
  have hU : (U : Matrix d d ℂ) * (U : Matrix d d ℂ)ᴴ = 1 := U.prop.2
  calc
    _ = ((U : Matrix d d ℂ) * (U : Matrix d d ℂ)ᴴ) * X *
        ((U : Matrix d d ℂ) * (U : Matrix d d ℂ)ᴴ) := by noncomm_ring
    _ = X := by rw [hU, Matrix.one_mul, Matrix.mul_one]

/-- Preprocessing acts by applying the preprocessing map to each ensemble state. -/
theorem holevoValue_precompose {α : Type*} [Fintype α] (Φ : CPTPMap d e)
    (Ψ : CPTPMap f d) (E : MEnsemble f α) :
    holevoValue (Φ ∘ₘ Ψ) E = holevoValue Φ (outputEnsemble Ψ E) := by
  unfold holevoValue
  rw [CPTPMap.compose_eq, channel_mix]
  rfl

/-- Every preprocessed ensemble value is an ensemble value of the original channel. -/
theorem holevoValues_precompose_subset (Φ : CPTPMap d e) (Ψ : CPTPMap f d) :
    holevoValues (Φ ∘ₘ Ψ) ⊆ holevoValues Φ := by
  rintro v ⟨k, E, rfl⟩
  exact ⟨k, outputEnsemble Ψ E, (holevoValue_precompose Φ Ψ E).symm⟩

/-- Unitary changes of input coordinates preserve Holevo information in nats. -/
theorem holevo_input_unitary (U : Matrix.unitaryGroup d ℂ) (Φ : CPTPMap d e) :
    holevo (Φ ∘ₘ CPTPMap.ofUnitary U) = holevo Φ := by
  unfold holevo
  congr 1
  refine Set.Subset.antisymm (holevoValues_precompose_subset _ _) ?_
  have h : Φ = (Φ ∘ₘ CPTPMap.ofUnitary U) ∘ₘ CPTPMap.ofUnitary (star U) := by
    rw [CPTPMap.compose_assoc, ofUnitary_comp_star, CPTPMap.compose_id]
  intro v hv
  rw [h] at hv
  exact holevoValues_precompose_subset _ _ hv

/-- Input conjugation commutes with tensoring by an arbitrary partner channel. -/
theorem prod_input_unitary (U : Matrix.unitaryGroup d ℂ) (Φ : CPTPMap d e)
    (Ω : CPTPMap f g) :
    (Φ ∘ₘ CPTPMap.ofUnitary U) ⊗ᶜᵖ Ω = (Φ ⊗ᶜᵖ Ω) ∘ₘ
      CPTPMap.ofUnitary (Matrix.unitary_kron U (1 : Matrix.unitaryGroup f ℂ)) := by
  calc
    _ = (Φ ∘ₘ CPTPMap.ofUnitary U) ⊗ᶜᵖ
        (Ω ∘ₘ CPTPMap.ofUnitary (1 : Matrix.unitaryGroup f ℂ)) := by
      rw [unitary_one, CPTPMap.compose_id]
    _ = (Φ ⊗ᶜᵖ Ω) ∘ₘ (CPTPMap.ofUnitary U ⊗ᶜᵖ
        CPTPMap.ofUnitary (1 : Matrix.unitaryGroup f ℂ)) := prod_compose _ _ _ _
    _ = _ := by rw [unitary_prod]

/-- Unitary input preprocessing preserves the product channel's Holevo information. -/
theorem holevo_prod_input_unitary (U : Matrix.unitaryGroup d ℂ) (Φ : CPTPMap d e)
    (Ω : CPTPMap f g) :
    holevo ((Φ ∘ₘ CPTPMap.ofUnitary U) ⊗ᶜᵖ Ω) = holevo (Φ ⊗ᶜᵖ Ω) := by
  rw [prod_input_unitary, holevo_input_unitary]

/-- Simultaneous input/output changes of coordinates preserve Holevo information. -/
theorem holevoInformation_unitary_coordinates (U : Matrix.unitaryGroup d ℂ)
    (V : Matrix.unitaryGroup e ℂ) (Φ : CPTPMap d e) :
    holevoInformation (CPTPMap.ofUnitary V ∘ₘ Φ ∘ₘ CPTPMap.ofUnitary U) =
      holevoInformation Φ := by
  unfold holevoInformation
  rw [holevo_input_unitary, holevo_output_unitary]

/-- The same invariance holds after tensoring with any finite-dimensional partner. -/
theorem holevoInformation_prod_unitary_coordinates (U : Matrix.unitaryGroup d ℂ)
    (V : Matrix.unitaryGroup e ℂ) (Φ : CPTPMap d e) (Ω : CPTPMap f g) :
    holevoInformation ((CPTPMap.ofUnitary V ∘ₘ Φ ∘ₘ CPTPMap.ofUnitary U) ⊗ᶜᵖ Ω) =
      holevoInformation (Φ ⊗ᶜᵖ Ω) := by
  unfold holevoInformation
  rw [holevo_prod_input_unitary, holevo_prod_output_unitary]

end SchurEntropy.PhaseCovariant
