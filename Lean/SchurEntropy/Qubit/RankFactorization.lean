import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Exact rank factorization of a rectangular complex matrix

Choose a basis of the range to obtain an injective left factor. The number
of columns is exactly the matrix rank, including the zero-rank case.
-/

noncomputable section
open scoped Matrix BigOperators ComplexConjugate

namespace SchurEntropy.Qubit

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- A rank factorization with an injective left factor. -/
theorem exists_rank_factor (B : Matrix n m ℂ) :
    ∃ L : Matrix n (Fin B.rank) ℂ, ∃ R : Matrix m (Fin B.rank) ℂ,
      Function.Injective L.mulVec ∧ B = L * Rᴴ := by
  classical
  let b := Module.finBasis ℂ (LinearMap.range B.mulVecLin)
  let L : Matrix n (Fin B.rank) ℂ := fun i j => (b j).val i
  let F : Matrix (Fin B.rank) m ℂ :=
    fun j k => b.repr (B.mulVecLin.rangeRestrict (Pi.single k 1)) j
  refine ⟨L, Fᴴ, ?_, ?_⟩
  · apply Matrix.mulVec_injective_iff.mpr
    change LinearIndependent ℂ (fun j => ((b j) : n → ℂ))
    exact b.linearIndependent.map' (LinearMap.range B.mulVecLin).subtype (Submodule.ker_subtype _)
  · rw [Matrix.conjTranspose_conjTranspose]
    ext i k
    have hb := congrArg (fun x : LinearMap.range B.mulVecLin => x.val i)
      (b.sum_repr (B.mulVecLin.rangeRestrict (Pi.single k 1)))
    change B i k = ∑ j, (b j).val i *
      b.repr (B.mulVecLin.rangeRestrict (Pi.single k 1)) j
    change (∑ j, b.repr (B.mulVecLin.rangeRestrict (Pi.single k 1)) j • b j).val i =
      B.mulVec (Pi.single k 1) i at hb
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single, op_smul_eq_smul,
      one_smul, Matrix.col_apply, mul_comm, mul_one] using hb.symm

end SchurEntropy.Qubit
