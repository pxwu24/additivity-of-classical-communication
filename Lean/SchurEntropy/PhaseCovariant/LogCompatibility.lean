import SchurEntropy.PhaseCovariant.ComparisonState
import SchurEntropy.Capacity.CriterionStatements
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! Diagonal optimal centers test only the diagonal of a channel output. No
invertibility assumption is imposed on the center. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped Matrix.Norms.L2Operator in
/-- Real functional calculus preserves the fixed diagonal subalgebra, even
for functions discontinuous away from the finite spectrum. -/
theorem cfc_diagonal_of_diagonal (A : Matrix d d ℂ)
    (hA : A = Matrix.diagonal A.diag) (f : ℝ → ℝ) :
    cfc f A = Matrix.diagonal (cfc f A).diag := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · simp only [Matrix.diagonal_apply_ne _ hij]
    let v : d → ℂ := fun k => if k = j then 1 else 0
    have hcomm : Commute A (Matrix.diagonal v) := by
      rw [hA]
      change Matrix.diagonal A.diag * Matrix.diagonal v =
        Matrix.diagonal v * Matrix.diagonal A.diag
      simp only [Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      exact mul_comm _ _
    have hc := congrArg (fun X : Matrix d d ℂ => X i j) (hcomm.cfc_real f).eq
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, v, hij] using hc

/-- Pairing against a diagonal logarithm depends only on the diagonal. -/
theorem logPairing_eq_of_diag_eq (σ ρ τ : MState d)
    (hσ : σ.m = Matrix.diagonal σ.m.diag)
    (hdiag : ∀ i, ρ.m i i = τ.m i i) :
    Capacity.logPairing σ ρ = Capacity.logPairing σ τ := by
  unfold Capacity.logPairing QubitAdditivity.BetaPowers.logarithm
  rw [cfc_diagonal_of_diagonal σ.m hσ Real.log]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun x => x * (cfc Real.log σ.m).diag i) (hdiag i)

/-- The same compatibility statement in the paper's base-two convention. -/
theorem logExpectation_eq_of_diag_eq (σ ρ τ : MState d)
    (hσ : σ.m = Matrix.diagonal σ.m.diag)
    (hdiag : ∀ i, ρ.m i i = τ.m i i) :
    Capacity.logExpectation σ ρ = Capacity.logExpectation σ τ := by
  unfold Capacity.logExpectation
  rw [logPairing_eq_of_diag_eq σ ρ τ hσ hdiag]

namespace NormalForm
variable {Φ : CPTPMap d d} (N : NormalForm Φ)

include N in
/-- The positive-amplitude input satisfies the weaker criterion's logarithmic
compatibility with any diagonal center. -/
theorem comparisonState_logPairing (σ ρ : MState d)
    (hσ : σ.m = Matrix.diagonal σ.m.diag) :
    Capacity.logPairing σ (Φ (comparisonState ρ)) = Capacity.logPairing σ (Φ ρ) :=
  logPairing_eq_of_diag_eq _ _ _ hσ (N.comparisonState_output_diag ρ)

include N in
/-- Base-two logarithmic compatibility for the comparison state. -/
theorem comparisonState_logExpectation (σ ρ : MState d)
    (hσ : σ.m = Matrix.diagonal σ.m.diag) :
    Capacity.logExpectation σ (Φ (comparisonState ρ)) = Capacity.logExpectation σ (Φ ρ) :=
  logExpectation_eq_of_diag_eq _ _ _ hσ (N.comparisonState_output_diag ρ)

end NormalForm
end SchurEntropy.PhaseCovariant
