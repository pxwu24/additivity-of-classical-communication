import SchurEntropy.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Tactic.FunProp

noncomputable section

open scoped BigOperators ComplexOrder
open Topology

namespace SchurEntropy

open scoped Matrix.Norms.L2Operator in
/-- Spectral entropy, including at zero eigenvalues, is continuous on
Hermitian matrices. This does not assert differentiability at the boundary. -/
theorem continuousOn_entropy {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousOn (entropy (ι := ι)) {A : Matrix ι ι ℂ | A.IsHermitian} := by
  have hc : ContinuousOn (fun A : Matrix ι ι ℂ => cfc Real.negMulLog A)
      {A : Matrix ι ι ℂ | A.IsHermitian} :=
    ContinuousOn.cfc_of_mem_nhdsSet Real.negMulLog (s := Set.univ)
      (by simp) continuousOn_id (fun _ hA => hA)
      Real.continuous_negMulLog.continuousOn
  have ht : Continuous (fun A : Matrix ι ι ℂ => (Matrix.trace A).re) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    fun_prop
  exact (ht.comp_continuousOn' hc).div_const (Real.log 2)

open scoped Matrix.Norms.L2Operator in
/-- In particular, entropy is continuous on the positive semidefinite cone. -/
theorem continuousOn_entropy_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContinuousOn (entropy (ι := ι)) {A : Matrix ι ι ℂ | A.PosSemidef} :=
  continuousOn_entropy.mono (fun _ hA => hA.isHermitian)

end SchurEntropy
