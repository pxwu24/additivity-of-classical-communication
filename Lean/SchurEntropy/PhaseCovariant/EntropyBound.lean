import SchurEntropy.PhaseCovariant.EntropyBoundWeights
import SchurEntropy.PhaseCovariant.BlockEntropyBridge

/-! The pure-input entropy estimate for every fixed-basis phase-covariant
normal form, derived from the Schur-weighted block entropy theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder
namespace SchurEntropy.PhaseCovariant

variable {d f g : Type*} [Fintype d] [DecidableEq d]
  [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]

namespace NormalForm
variable {Φ : CPTPMap d d} (N : NormalForm Φ)

theorem joint_output_m (Ω : CPTPMap f g) (ψ : Ket (d × f)) :
    ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ)).m =
      productSchur N.C (partnerBlocks Ω ψ) + productDiagonal (N.noiseBlock Ω ψ) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [N.joint_output_entry]
  simp

theorem comparison_output_m (ψ : Ket (d × f)) :
    (Φ (comparisonState (MState.pure ψ).traceRight)).m =
      traceSkeleton N.C (branchMass ψ) +
        Matrix.diagonal (fun i => (N.noiseWeights (branchMass ψ) i : ℂ)) := by
  have hcomp : comparisonState (MState.pure ψ).traceRight =
      sqrtState (branchMass ψ) (branchMass_nonneg ψ) (branchMass_sum ψ) := by
    apply MState.ext_m
    ext i j
    simp only [comparisonState_m, sqrtState_m, branchMass_eq_marginal_diag]
  rw [hcomp]
  ext i j
  rw [N.sqrtState_output_entry]
  simp only [Matrix.add_apply, traceSkeleton_apply, Matrix.diagonal_apply]
  ring

include N in
/-- The entropy estimate used in the weaker entropic additivity criterion.
The comparison state lives on the original input space in its fixed basis.
The partner ensemble includes zero branches with zero probability. -/
theorem pure_entropy_bound [Nonempty f] (Ω : CPTPMap f g) (ψ : Ket (d × f)) :
    Sᵥₙ (Φ (comparisonState (MState.pure ψ).traceRight)) +
      avgOutputEntropy Ω (branchEnsemble ψ) ≤
      Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ)) := by
  let : Nonempty d := (MState.pure ψ).traceRight.nonempty
  let : Nonempty g := (Ω (default : MState f)).nonempty
  rw [branchEnsemble_avg]
  simp only [entropy_eq_openai]
  have hb := block_entropy_product N.C (partnerBlocks Ω ψ) (N.noiseBlock Ω ψ)
    (branchMass ψ) (N.noiseWeights (branchMass ψ)) N.C_psd (partnerBlocks_psd Ω ψ)
    (N.noiseBlock_psd Ω ψ) (partnerBlocks_trace Ω ψ) (N.noiseBlock_trace Ω ψ)
  rw [← N.comparison_output_m ψ, ← N.joint_output_m Ω ψ] at hb
  have hn := N.internal_entropy_ge Ω ψ
  linarith

end NormalForm
end SchurEntropy.PhaseCovariant
