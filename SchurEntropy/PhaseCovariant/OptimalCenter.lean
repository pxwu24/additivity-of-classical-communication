import SchurEntropy.PhaseCovariant.Definitions
import SchurEntropy.PhaseCovariant.SignAveraging
import SchurEntropy.Capacity.OptimalEnsemble

/-! # A diagonal center attained by an optimal ensemble

Finite averaging over diagonal sign unitaries preserves average output entropy,
while entropy concavity increases the entropy of the average output. Applying
this to an actual maximizing ensemble gives another actual maximizer whose
output average is diagonal. No uniqueness premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace SchurEntropy.PhaseCovariant
open QubitAdditivity QubitAdditivity.BetaSignFrame SchurEntropy.Capacity

@[reducible] local instance optimalMatrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α : Type*} [Fintype α]

/-- Phase covariance acts on density matrices under each finite sign unitary. -/
theorem phaseCovariant_sign_action {Φ : CPTPMap d d} (hΦ : PhaseCovariant Φ)
    (f : d → Bool) (ρ : MState d) :
    Φ (CPTPMap.ofUnitary (signUnitary f) ρ) =
      CPTPMap.ofUnitary (signUnitary f) (Φ ρ) := by
  apply MState.ext_m
  simp only [CPTPMap.mat_coe_eq_apply_mat]
  exact hΦ (fun i => sign (f i)) (fun i => norm_sign (f i)) ρ.m

/-- Uniform sign rotations of every input in an ensemble. -/
def signSymmetrizedEnsemble (E : MEnsemble d α) :
    MEnsemble d (Σ _ : d → Bool, α) :=
  sigmaEnsemble ProbDistribution.uniform
    (fun f => outputEnsemble (CPTPMap.ofUnitary (signUnitary f)) E)

/-- Covariance identifies the symmetrized output average with its sign orbit. -/
theorem signSymmetrizedEnsemble_center {Φ : CPTPMap d d} (hΦ : PhaseCovariant Φ)
    (E : MEnsemble d α) :
    Φ (Ensemble.mix (signSymmetrizedEnsemble E)) =
      Ensemble.mix (signOrbit (Φ (Ensemble.mix E))) := by
  apply MState.ext_m
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change Φ.map (Ensemble.mix (sigmaEnsemble ProbDistribution.uniform
    (fun f => outputEnsemble (CPTPMap.ofUnitary (signUnitary f)) E))).m = _
  rw [sigmaEnsemble_mix, map_sum, Ensemble.mix_of]
  apply Finset.sum_congr rfl
  intro f _
  rw [Φ.map.map_smul_of_tower]
  congr 1
  rw [← CPTPMap.mat_coe_eq_apply_mat, ← channel_mix, phaseCovariant_sign_action hΦ]
  rfl

/-- Every rotated ensemble has exactly the original average output entropy. -/
theorem signSymmetrizedEnsemble_avgOutputEntropy {Φ : CPTPMap d d}
    (hΦ : PhaseCovariant Φ) (E : MEnsemble d α) :
    avgOutputEntropy Φ (signSymmetrizedEnsemble E) = avgOutputEntropy Φ E := by
  unfold avgOutputEntropy signSymmetrizedEnsemble
  rw [sigmaEnsemble_sum ProbDistribution.uniform
    (fun f => outputEnsemble (CPTPMap.ofUnitary (signUnitary f)) E)
    (fun ρ => Sᵥₙ (Φ ρ))]
  have hf (f : d → Bool) :
      (∑ j, ((outputEnsemble (CPTPMap.ofUnitary (signUnitary f)) E).distr j : ℝ) *
        Sᵥₙ (Φ ((outputEnsemble (CPTPMap.ofUnitary (signUnitary f)) E).states j))) =
      ∑ j, (E.distr j : ℝ) * Sᵥₙ (Φ (E.states j)) := by
    apply Finset.sum_congr rfl
    intro j _
    change (E.distr j : ℝ) * Sᵥₙ (Φ (CPTPMap.ofUnitary (signUnitary f) (E.states j))) = _
    rw [phaseCovariant_sign_action hΦ, RotationInvariant.entropy_output_unitary]
  simp only [hf, ← Finset.sum_mul, ProbDistribution.normalized, one_mul]

/-- Sign symmetrization can only increase the Holevo value. -/
theorem holevoValue_le_signSymmetrizedEnsemble {Φ : CPTPMap d d}
    (hΦ : PhaseCovariant Φ) (E : MEnsemble d α) :
    holevoValue Φ E ≤ holevoValue Φ (signSymmetrizedEnsemble E) := by
  rw [holevoValue_eq, holevoValue_eq, signSymmetrizedEnsemble_avgOutputEntropy hΦ,
    signSymmetrizedEnsemble_center hΦ]
  exact sub_le_sub_right (entropy_signOrbit_mix (Φ (Ensemble.mix E))) _

/-- The sign-symmetrized ensemble has diagonal average output. -/
theorem signSymmetrizedEnsemble_center_diagonal {Φ : CPTPMap d d}
    (hΦ : PhaseCovariant Φ) (E : MEnsemble d α) :
    (Φ (Ensemble.mix (signSymmetrizedEnsemble E))).m =
      Matrix.diagonal (fun i => (Φ (Ensemble.mix (signSymmetrizedEnsemble E))).m i i) := by
  rw [signSymmetrizedEnsemble_center hΦ, signOrbit_mix]
  simp only [Matrix.diagonal_apply_eq]

/-- An actual optimal finite ensemble can be chosen with a diagonal output
center, in the same fixed basis as phase covariance. -/
theorem exists_diagonal_optimal_ensemble [Nonempty d] (Φ : CPTPMap d d)
    (hΦ : PhaseCovariant Φ) :
    ∃ (k : ℕ) (E : MEnsemble d (Fin k)), OptimalEnsemble Φ E ∧
      (Φ (Ensemble.mix E)).m = Matrix.diagonal (fun i => (Φ (Ensemble.mix E)).m i i) := by
  obtain ⟨k, E, hE⟩ := exists_optimal_ensemble Φ
  let σ := Fintype.equivFin (Σ _ : d → Bool, Fin k)
  let F := Ensemble.congrMEnsemble σ (signSymmetrizedEnsemble E)
  refine ⟨Fintype.card (Σ _ : d → Bool, Fin k), F, ?_, ?_⟩
  · rw [optimalEnsemble_iff_nat]
    apply le_antisymm (holevoValue_le_holevo Φ F)
    change holevo Φ ≤ holevoValue Φ (Ensemble.congrMEnsemble σ (signSymmetrizedEnsemble E))
    rw [holevoValue_reindex, ← hE]
    exact holevoValue_le_signSymmetrizedEnsemble hΦ E
  · change (Φ (Ensemble.mix (Ensemble.congrMEnsemble σ (signSymmetrizedEnsemble E)))).m = _
    rw [Ensemble.mix_congrMEnsemble_eq_mix]
    exact signSymmetrizedEnsemble_center_diagonal hΦ E

end SchurEntropy.PhaseCovariant
