import SchurEntropy.Qubit.ChannelBoundAlgebra
import SchurEntropy.Qubit.EnsembleBound
import SchurEntropy.Qubit.BlockEntropyBridge
import SchurEntropy.Capacity.StandardCriterion

/-! The pure-input entropic criterion for a single coherent Kraus branch.
Finite branch ensembles and the joint-output reduction are adapted from the
pinned QubitAdditivity.PureInput; arbitrary finite input dimension is allowed. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix QubitAdditivity

namespace SchurEntropy.Qubit
namespace QubitOutputForm

variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K]
variable (N : QubitOutputForm D J K)
variable {dB eB : Type*} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]

/-- The branch vectors of `ψ`, grouped by output row: `a`, the `b j`, then `c`, the `d k`. -/
def branches (ψ : D × dB → ℂ) : (Unit ⊕ J) ⊕ (Unit ⊕ K) → dB → ℂ
  | .inl (.inl _) => branch N.a ψ
  | .inl (.inr j) => branch (N.b j) ψ
  | .inr (.inl _) => branch N.c ψ
  | .inr (.inr k) => branch (N.d k) ψ

omit [DecidableEq dB] in
theorem sum_branches {X : Type*} [AddCommMonoid X] (ψ : D × dB → ℂ) (f : (dB → ℂ) → X) :
    ∑ x, f (N.branches ψ x) =
      f (branch N.a ψ) + ∑ j, f (branch (N.b j) ψ) +
        (f (branch N.c ψ) + ∑ k, f (branch (N.d k) ψ)) := by
  simp [Fintype.sum_sum_type, branches]

theorem branches_mass (h : N.Complete) (ψ : Ket (D × dB)) :
    ∑ x, vecMass (N.branches ψ x) = 1 := by
  have ht := congrArg (fun M => (Matrix.trace M).re) (N.traceLeft_pure_eq h ψ)
  simp only [MState.tr', Complex.one_re, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, trace_vecMulVec_re] at ht
  rw [N.sum_branches ψ vecMass]
  linarith

theorem mass_eq (W : (eB × dB) → Matrix eB dB ℂ) (hW1 : ∑ k, (W k)ᴴ * W k = 1)
    (ψ : Ket (D × dB)) :
    blockMass (N.blockA W ψ) = N.mx (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockB W ψ) = N.my (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockC W ψ) = N.mz (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockD W ψ) = N.mw (MState.pure ψ).traceRight.m := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [blockA, blockB, blockC, blockD, blockMass_branchBlock W hW1, vecMass_branch, mx, my,
      mz, mw]

/-- The assembly step: the scalar ensemble estimate and the two-row block
entropy inequality imply the exact standard entropic criterion. -/
theorem pureInputBound_of_bounds (h : N.Complete) [Nonempty D] [Nonempty dB]
    (Ω : CPTPMap dB eB)
    (hscalar : ∀ ρ : MState D, ∃ (k : ℕ) (E : MEnsemble D (Fin k)), Ensemble.mix E = ρ ∧
      avgOutputEntropy (N.toCPTP h) E ≤
        OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx ρ.m) (N.my ρ.m) (N.mz ρ.m) (N.mw ρ.m)))
    (hblock : ∀ (A : Matrix eB (Unit × (eB × dB)) ℂ)
      (B : Matrix eB (J × (eB × dB)) ℂ) (C : Matrix eB (Unit × (eB × dB)) ℂ)
      (D' : Matrix eB (K × (eB × dB)) ℂ),
      OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B)
        (blockMass C) (blockMass D')) + weightedBlockEntropy A + weightedBlockEntropy B +
        weightedBlockEntropy C + weightedBlockEntropy D' ≤
      OpenAIEntropy.entropy (tc4Matrix A B C D' * (tc4Matrix A B C D').conjTranspose)) :
    PureInputBound (N.toCPTP h) Ω := by
  intro ψ
  obtain ⟨W, hW, hW1⟩ := exists_kraus_family Ω
  obtain ⟨k, E, hmixA, hscalarA⟩ := hscalar (MState.pure ψ).traceRight
  have hmass := N.branches_mass h ψ
  let σF := Fintype.equivFin ((Unit ⊕ J) ⊕ (Unit ⊕ K))
  refine ⟨k, Fintype.card ((Unit ⊕ J) ⊕ (Unit ⊕ K)), E,
    Ensemble.congrMEnsemble σF (vecEnsemble (N.branches ψ) hmass), hmixA, ?_, ?_⟩
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    apply MState.ext_m
    rw [vecEnsemble_mix_m, N.sum_branches ψ (fun η => vecMulVec η (star η)),
      N.traceLeft_pure_eq h ψ]
    abel
  · rw [avgOutputEntropy_reindex, avgOutputEntropy_vecEnsemble,
      N.sum_branches ψ (fun η => vecMass η * Sᵥₙ (Ω (vecState η)))]
    obtain ⟨hmA, hmB, hmC, hmD⟩ := N.mass_eq W hW1 ψ
    have hT := hblock (N.blockA W ψ) (N.blockB W ψ) (N.blockC W ψ) (N.blockD W ψ)
    rw [hmA, hmB, hmC, hmD] at hT
    have hA := weightedBlockEntropy_branchBlock_ge Ω W hW (fun _ : Unit => branch N.a ψ)
    have hB := weightedBlockEntropy_branchBlock_ge Ω W hW (fun j => branch (N.b j) ψ)
    have hC := weightedBlockEntropy_branchBlock_ge Ω W hW (fun _ : Unit => branch N.c ψ)
    have hD := weightedBlockEntropy_branchBlock_ge Ω W hW (fun j => branch (N.d j) ψ)
    simp only [Fintype.univ_punit, Finset.sum_singleton] at hA hC
    have hjoint : Sᵥₙ ((N.toCPTP h ⊗ᶜᵖ Ω) (MState.pure ψ)) =
        OpenAIEntropy.entropy (N.tc4At W ψ * (N.tc4At W ψ).conjTranspose) := by
      rw [entropy_eq_openai, N.joint_output_m h Ω W hW ψ]
      exact QubitAdditivity.entropy_submatrix_equiv _ (Matrix.isHermitian_mul_conjTranspose_self _)
    rw [hjoint]
    unfold tc4At
    simp only [blockA, blockB, blockC, blockD] at hT ⊢
    linarith

/-- A single coherent Kraus branch with commuting-output noise satisfies the
standard entropic criterion. The block estimate is supplied by the proved
Schur-weighted block entropy theorem, and the scalar ensemble is constructed. -/
theorem pureInputBound (h : N.Complete) [Nonempty D] [Nonempty dB]
    (Ω : CPTPMap dB eB) : PureInputBound (N.toCPTP h) Ω := by
  letI : Nonempty eB := (Ω (default : MState dB)).nonempty
  apply N.pureInputBound_of_bounds h Ω (N.scalar_bound h)
  intro A B C D'
  exact tc4_equal_rows_of_blockEntropy A B C D'

/-- The same complete criterion expressed in the manuscript's entropy in bits. -/
theorem standardEntropicCriterion (h : N.Complete) [Nonempty D] [Nonempty dB]
    (Ω : CPTPMap dB eB) : SchurEntropy.Capacity.StandardEntropicCriterion (N.toCPTP h) Ω :=
  (SchurEntropy.Capacity.standardEntropicCriterion_iff_pureInputBound _ _).mpr
    (N.pureInputBound h Ω)

end QubitOutputForm
end SchurEntropy.Qubit
