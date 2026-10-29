import SchurEntropy.PhaseCovariant.Definitions
import SchurEntropy.Qubit.ChannelBoundAlgebra

/-! Matrix identities and marginal ensembles for a phase-covariant channel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder Kronecker MatrixMap
namespace SchurEntropy.PhaseCovariant

variable {d f g : Type*} [Fintype d] [DecidableEq d]
  [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]

/-- The unnormalized partner vector attached to a fixed input basis vector. -/
def inputBranch (ψ : d × f → ℂ) (i : d) : f → ℂ := fun x => ψ (i, x)

/-- The corresponding squared norm. Zero branches are retained with zero weight. -/
def branchMass (ψ : d × f → ℂ) (i : d) : ℝ := vecMass (inputBranch ψ i)

omit [Fintype d] [DecidableEq d] in
theorem branchMass_nonneg (ψ : d × f → ℂ) (i : d) : 0 ≤ branchMass ψ i :=
  vecMass_nonneg _

theorem branch_outer_sum (ψ : Ket (d × f)) :
    ∑ i, vecMulVec (inputBranch ψ i) (star (inputBranch ψ i)) =
      (MState.pure ψ).traceLeft.m := by
  rw [SchurEntropy.Qubit.traceLeft_pure_m]
  ext x y
  simp [inputBranch, Matrix.sum_apply, vecMulVec_apply]

theorem branchMass_sum (ψ : Ket (d × f)) : ∑ i, branchMass ψ i = 1 := by
  have ht := congrArg (fun X => (Matrix.trace X).re) (branch_outer_sum ψ)
  simpa only [Matrix.trace_sum, Complex.re_sum, trace_vecMulVec_re,
    MState.tr', Complex.one_re, branchMass] using ht

theorem branchMass_eq_marginal_diag (ψ : Ket (d × f)) (i : d) :
    branchMass ψ i = ((MState.pure ψ).traceRight.m i i).re := by
  rw [SchurEntropy.Qubit.traceRight_pure_m]
  simp [branchMass, inputBranch, vecMass, Complex.mul_conj, Complex.re_sum]

theorem marginal_diag_eq_branchMass (ψ : Ket (d × f)) (i : d) :
    (MState.pure ψ).traceRight.m i i = (branchMass ψ i : ℂ) := by
  rw [SchurEntropy.Qubit.traceRight_pure_m]
  simp [branchMass, inputBranch, vecMass, Complex.mul_conj, Complex.ofReal_sum]

/-- The normalized partner branches, with their original squared-norm weights. -/
def branchEnsemble [Nonempty f] (ψ : Ket (d × f)) : MEnsemble f d :=
  vecEnsemble (inputBranch ψ) (branchMass_sum ψ)

theorem branchEnsemble_mix [Nonempty f] (ψ : Ket (d × f)) :
    Ensemble.mix (branchEnsemble ψ) =
      (MState.pure ψ).traceLeft := by
  apply MState.ext_m
  unfold branchEnsemble
  rw [vecEnsemble_mix_m, branch_outer_sum]

theorem branchEnsemble_avg [Nonempty f] (Ω : CPTPMap f g) (ψ : Ket (d × f)) :
    avgOutputEntropy Ω (branchEnsemble ψ) =
      ∑ i, branchMass ψ i * Sᵥₙ (Ω (vecState (inputBranch ψ i))) := rfl

omit [Fintype g] [DecidableEq g] in
/-- A linear matrix map expanded in matrix units. -/
theorem matrixMap_entry_sum (M : MatrixMap f g ℂ) (X : Matrix f f ℂ) (x y : g) :
    M X x y = ∑ a, ∑ b, X a b * M (Matrix.single a b 1) x y := by
  have hX : X = ∑ a, ∑ b, X a b • (Matrix.single a b 1 : Matrix f f ℂ) := by
    ext i j
    simp [Matrix.single, Matrix.sum_apply, ite_and]
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq g] in
/-- A tensor-product channel acts on its partner blocks before applying the first map. -/
theorem kron_entry_blocks (M : MatrixMap d d ℂ) (N : MatrixMap f g ℂ)
    (X : Matrix (d × f) (d × f) ℂ) (i j : d) (x y : g) :
    (M ⊗ₖₘ N) X (i,x) (j,y) =
      M (fun a b => N (fun u v => X (a,u) (b,v)) x y) i j := by
  rw [MatrixMap.kron_def]
  conv_rhs => rw [matrixMap_entry_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [matrixMap_entry_sum N (fun u v => X (a,u) (b,v)) x y]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/-- The positive block matrix obtained by applying only the partner channel. -/
def partnerBlocks (Ω : CPTPMap f g) (ψ : d × f → ℂ) : Matrix (d × g) (d × g) ℂ :=
  fun a b => Ω.map (vecMulVec (inputBranch ψ a.1) (star (inputBranch ψ b.1))) a.2 b.2

omit [DecidableEq g] in
theorem partnerBlocks_eq (Ω : CPTPMap f g) (ψ : Ket (d × f)) :
    partnerBlocks Ω ψ =
      (MatrixMap.id d ℂ ⊗ₖₘ Ω.map) (MState.pure ψ).m := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [kron_entry_blocks, pure_m]
  rfl

omit [DecidableEq g] in
theorem partnerBlocks_psd (Ω : CPTPMap f g) (ψ : Ket (d × f)) :
    (partnerBlocks Ω ψ).PosSemidef := by
  rw [partnerBlocks_eq]
  exact (MatrixMap.IsCompletelyPositive.id.kron Ω.cp).IsPositive (MState.pure ψ).psd

omit [Fintype d] [DecidableEq d] in
theorem partnerBlocks_diagonal [Nonempty f] (Ω : CPTPMap f g)
    (ψ : d × f → ℂ) (i : d) :
    (partnerBlocks Ω ψ).submatrix (fun x => (i,x)) (fun x => (i,x)) =
      branchMass ψ i • (Ω (vecState (inputBranch ψ i))).m := by
  change Ω.map (vecMulVec (inputBranch ψ i) (star (inputBranch ψ i))) = _
  rw [← vecMass_smul_vecState_m, CPTPMap.mat_coe_eq_apply_mat,
    Ω.map.map_smul_of_tower]
  rfl

omit [Fintype d] [DecidableEq d] [DecidableEq g] in
theorem partnerBlocks_trace (Ω : CPTPMap f g) (ψ : d × f → ℂ) (i : d) :
    (Matrix.trace ((partnerBlocks Ω ψ).submatrix (fun x => (i,x))
      (fun x => (i,x)))).re = branchMass ψ i := by
  change (Matrix.trace (Ω.map (vecMulVec (inputBranch ψ i)
    (star (inputBranch ψ i))))).re = _
  rw [Ω.TP, trace_vecMulVec_re]
  rfl

namespace NormalForm
variable {Φ : CPTPMap d d} (N : NormalForm Φ)

/-- The commuting noise in output block `i`. -/
def noiseBlock (Ω : CPTPMap f g) (ψ : d × f → ℂ) (i : d) : Matrix g g ℂ :=
  ∑ j, if i ≠ j then N.p i j •
    ((partnerBlocks Ω ψ).submatrix (fun x => (j,x)) (fun x => (j,x))) else 0

omit [DecidableEq g] in
theorem noiseBlock_psd (Ω : CPTPMap f g) (ψ : Ket (d × f)) (i : d) :
    (N.noiseBlock Ω ψ i).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  split_ifs
  · exact ((partnerBlocks_psd Ω ψ).submatrix _).smul (N.p_nonneg i j)
  · exact Matrix.PosSemidef.zero

theorem joint_output_entry (Ω : CPTPMap f g) (ψ : Ket (d × f))
    (i j : d) (x y : g) :
    ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ)).m (i,x) (j,y) =
      N.C i j * partnerBlocks Ω ψ (i,x) (j,y) +
        if i = j then N.noiseBlock Ω ψ i x y else 0 := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (Φ.map ⊗ₖₘ Ω.map) (MState.pure ψ).m (i,x) (j,y) = _
  rw [kron_entry_blocks, N.action, pure_m]
  simp only [Matrix.add_apply, Matrix.hadamard_apply, Matrix.diagonal_apply]
  congr 1
  split_ifs with h
  · subst j
    simp only [noiseBlock, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp [Complex.real_smul, partnerBlocks, vecMulVec_apply]
    exact Or.inl rfl
  · rfl

end NormalForm
end SchurEntropy.PhaseCovariant
