import SchurEntropy.Capacity.Definitions
import SchurEntropy.Capacity.OptimalEnsemble

noncomputable section

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {d e : Type*} [Fintype d] [DecidableEq d]
variable [Fintype e] [DecidableEq e] [Nonempty d]

/-- Size of a finite ensemble actually attaining the Holevo supremum. -/
def optimalEnsembleSize (Φ : CPTPMap d e) : ℕ :=
  (exists_optimal_ensemble Φ).choose

/-- One attaining ensemble, chosen from the proved existence theorem. -/
def chosenOptimalEnsemble (Φ : CPTPMap d e) : MEnsemble d (Fin (optimalEnsembleSize Φ)) :=
  (exists_optimal_ensemble Φ).choose_spec.choose

theorem chosenOptimalEnsemble_nat (Φ : CPTPMap d e) :
    holevoValue Φ (chosenOptimalEnsemble Φ) = holevo Φ :=
  (exists_optimal_ensemble Φ).choose_spec.choose_spec

theorem chosenOptimalEnsemble_optimal (Φ : CPTPMap d e) :
    OptimalEnsemble Φ (chosenOptimalEnsemble Φ) :=
  (optimalEnsemble_iff_nat Φ _).mpr (chosenOptimalEnsemble_nat Φ)

/-- The average output of an attaining ensemble. This definition contains
no assumed entropy bound or relative-entropy characterization. -/
def optimalOutputCenter (Φ : CPTPMap d e) : MState e :=
  Φ (Ensemble.mix (chosenOptimalEnsemble Φ))

end SchurEntropy.Capacity
