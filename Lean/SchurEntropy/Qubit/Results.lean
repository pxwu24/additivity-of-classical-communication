import SchurEntropy.Qubit.ChannelBound
import SchurEntropy.Qubit.DecompositionGeneral
import QubitAdditivity.RotationInvariant

/-!
# Strong Holevo additivity for the manuscript's qubit-output class

The first theorem permits arbitrary finite input dimension and a single
coherent Kraus operator plus two positive effects with commuting outputs.
The second theorem covers every qubit-to-qubit channel, using its proved
decomposition. Both conclusions use the actual finite-ensemble Holevo
information in bits.
-/

noncomputable section
open Matrix QubitAdditivity
open scoped Matrix BigOperators ComplexOrder MatrixMap

namespace SchurEntropy.Qubit
open SchurEntropy.Capacity QubitAdditivity.RotationInvariant

variable {D dB eB : Type*}
variable [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype dB] [DecidableEq dB] [Nonempty dB]
variable [Fintype eB] [DecidableEq eB]

/-- Result 2, in arbitrary finite input dimension. The unitary specifies the
output basis; its representation is an equality on all complex matrices.
The positive effects and coherent vectors may be singular or zero. -/
theorem single_coherent_qubit_output_additivity
    (Φ : CPTPMap D (Fin 2)) (Ω : CPTPMap dB eB)
    (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (a c : D → ℂ) (E₀ E₁ : Matrix D D ℂ)
    (h₀ : E₀.PosSemidef) (h₁ : E₁.PosSemidef)
    (hcomplete : vecMulVec a (star a) + vecMulVec c (star c) + E₀ + E₁ = 1)
    (hact : ∀ X : Matrix D D ℂ,
      (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = singleCoherentAction a c E₀ E₁ X) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  obtain ⟨N, hN, hform⟩ := exists_outputForm_of_effects a c E₀ E₁ h₀ h₁ hcomplete
  have heq : N.toCPTP hN = CPTPMap.ofUnitary U ∘ₘ Φ := by
    apply CPTPMap.ext
    apply LinearMap.ext
    intro X
    change MatrixMap.of_kraus N.kraus N.kraus X =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
    rw [N.act_eq_of_kraus, hact X]
    exact hform X
  have hcriterion := (standardEntropicCriterion_iff_pureInputBound (N.toCPTP hN) Ω).mpr
    (N.pureInputBound hN Ω)
  have hadd := standard_entropic_criterion (N.toCPTP hN) Ω hcriterion
  simpa only [heq, holevoInformation, holevo_prod_output_unitary, holevo_output_unitary]
    using hadd

/-- Every qubit-to-qubit channel has strongly additive Holevo information,
against every finite-dimensional partner channel. -/
theorem all_qubit_channels_additivity
    (Φ : CPTPMap (Fin 2) (Fin 2)) (Ω : CPTPMap dB eB) :
    holevoInformation (Φ ⊗ᶜᵖ Ω) = holevoInformation Φ + holevoInformation Ω := by
  have hdecomp := exists_qubit_output_decomposition_general Φ
  rw [Fintype.card_fin] at hdecomp
  obtain ⟨U, a, c, E₀, E₁, h₀, h₁, hcomplete, hact⟩ := hdecomp
  apply single_coherent_qubit_output_additivity Φ Ω U (a 0) (c 0) E₀ E₁ h₀ h₁
  · simpa only [Fintype.card_fin, Nat.reduceSub, Fin.sum_univ_one] using hcomplete
  · intro X
    simpa only [Fintype.card_fin, Nat.reduceSub, Fin.sum_univ_one, singleCoherentAction]
      using hact X

end SchurEntropy.Qubit
