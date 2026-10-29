/-
Adapted in part from KitaKen1/qubit-strong-additivity,
lean/QubitAdditivity/BetaValueHessian.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945 (Apache-2.0).
The vector pinching and diagonal-coordinate construction is generalized
from two blocks to a finite dependent family.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/
import SchurEntropy.MultiBlockOperators

/-! # Vector coordinates for finite block operators -/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace SchurEntropy.MultiBlock
open BlockAlgebra

def vector {ι : Type*} (A : Matrix ι ι ℂ) : ι × ι → ℂ := fun a => A a.1 a.2

variable {m : ℕ} (n : Fin m → ℕ)

def blockVector (W : Matrices n) : DiagonalUnitIndex n → ℂ :=
  fun a => W a.1 a.2.1 a.2.2

theorem vector_pinch (H : BlockMatrix n) :
    blockVector n (diagonalBlock n H) = (blockInclusion n)ᴴ *ᵥ vector H := by
  ext ⟨i, a, b⟩
  simp [blockVector, diagonalBlock, vector, blockInclusion, coordinateInclusion,
    Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Fintype.sum_eq_single (⟨i, a⟩, ⟨i, b⟩)]
  · simp
  · intro q hq
    simp [hq]

theorem vector_diagonal (W : Matrices n) :
    vector (Matrix.blockDiagonal' W) = blockInclusion n *ᵥ blockVector n W := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩
  simp [vector, blockVector, blockInclusion, coordinateInclusion,
    Matrix.mulVec, dotProduct, Matrix.one_apply,
    Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single i]
  · by_cases hij : i = j
    · subst j
      simp [Prod.mk.injEq, ite_and]
    · simp [Prod.mk.injEq, Matrix.blockDiagonal'_apply_ne, hij, Ne.symm hij]
  · intro k hk
    simp [Prod.mk.injEq, Ne.symm hk]

theorem blockVector_diagonal_mulVec (A : ∀ i, Matrix (Fin (n i) × Fin (n i))
    (Fin (n i) × Fin (n i)) ℂ) (W : Matrices n) :
    (Matrix.blockDiagonal' A) *ᵥ blockVector n W =
      fun p => (A p.1 *ᵥ vector (W p.1)) p.2 := by
  ext ⟨i, a, b⟩
  rw [diagonal_mulVec]
  rfl

end SchurEntropy.MultiBlock
