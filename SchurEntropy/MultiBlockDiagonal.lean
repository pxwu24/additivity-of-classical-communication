/-
Adapted in part from KitaKen1/qubit-strong-additivity,
lean/QubitAdditivity/BetaBlocks.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945 (Apache-2.0).
The functional-calculus homomorphism is generalized from two blocks to a
finite dependent family. Additional positivity arguments are proved here.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/
import SchurEntropy.BlockAlgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Functional calculus and positivity for finite dependent block sums -/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace SchurEntropy.MultiBlock

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [∀ i, DecidableEq (κ i)] in
@[simp] theorem diagonal_mulVec (A : ∀ i, Matrix (κ i) (κ i) ℂ)
    (v : (Σ i, κ i) → ℂ) (i : ι) (a : κ i) :
    ((Matrix.blockDiagonal' A) *ᵥ v) ⟨i, a⟩ =
      ((A i) *ᵥ (fun b => v ⟨i, b⟩)) a := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Matrix.blockDiagonal'_apply']

omit [∀ i, DecidableEq (κ i)] in
theorem diagonal_quadratic (A : ∀ i, Matrix (κ i) (κ i) ℂ)
    (v : (Σ i, κ i) → ℂ) :
    star v ⬝ᵥ ((Matrix.blockDiagonal' A) *ᵥ v) =
      ∑ i, star (fun b => v ⟨i, b⟩) ⬝ᵥ ((A i) *ᵥ (fun b => v ⟨i, b⟩)) := by
  simp [dotProduct, Fintype.sum_sigma]

omit [∀ i, DecidableEq (κ i)] in
theorem diagonal_posSemidef {A : ∀ i, Matrix (κ i) (κ i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) : (Matrix.blockDiagonal' A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_blockDiagonal'_iff.mpr (fun i => (hA i).1))
  intro v
  rw [diagonal_quadratic]
  exact Finset.sum_nonneg (fun i _ => (hA i).dotProduct_mulVec_nonneg _)

omit [∀ i, DecidableEq (κ i)] in
theorem diagonal_posDef {A : ∀ i, Matrix (κ i) (κ i) ℂ}
    (hA : ∀ i, (A i).PosDef) : (Matrix.blockDiagonal' A).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_blockDiagonal'_iff.mpr (fun i => (hA i).1))
  intro v hv
  rw [diagonal_quadratic]
  apply Finset.sum_pos'
    (fun i _ => (hA i).posSemidef.dotProduct_mulVec_nonneg _)
  obtain ⟨⟨i, a⟩, ha⟩ := Function.ne_iff.mp hv
  refine ⟨i, Finset.mem_univ i, (hA i).dotProduct_mulVec_pos ?_⟩
  intro hz
  exact ha (congrFun hz a)

/-- Direct-sum assembly as a unital real star-algebra homomorphism. -/
def diagonalHom : (∀ i, Matrix (κ i) (κ i) ℂ) →⋆ₐ[ℝ] Matrix (Σ i, κ i) (Σ i, κ i) ℂ where
  toFun := Matrix.blockDiagonal'
  map_one' := Matrix.blockDiagonal'_one
  map_mul' A B := Matrix.blockDiagonal'_mul A B
  map_zero' := Matrix.blockDiagonal'_zero
  map_add' A B := Matrix.blockDiagonal'_add A B
  commutes' c := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal'_smul]
  map_star' A := by
    simp only [star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
    rfl

theorem diagonal_inv (A : ∀ i, Matrix (κ i) (κ i) ℂ) (hA : ∀ i, IsUnit (A i)) :
    (Matrix.blockDiagonal' A)⁻¹ = Matrix.blockDiagonal' (fun i => (A i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal'_mul]
  have he : (fun i => (A i)⁻¹ * A i) = fun i => (1 : Matrix (κ i) (κ i) ℂ) := by
    funext i
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hA i))
  rw [he]
  exact Matrix.blockDiagonal'_one

open scoped Matrix.Norms.L2Operator in
theorem cfc_diagonal (A : ∀ i, Matrix (κ i) (κ i) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal' A) = Matrix.blockDiagonal' (fun i => cfc f (A i)) := by
  have : ContinuousFunctionalCalculus ℂ (∀ i, Matrix (κ i) (κ i) ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have : ContinuousFunctionalCalculus ℝ (∀ i, Matrix (κ i) (κ i) ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hf : ContinuousOn f (⋃ i, spectrum ℝ (A i)) :=
    (Set.finite_iUnion (fun i => Set.toFinite (spectrum ℝ (A i)))).continuousOn f
  have hself : IsSelfAdjoint A := funext hA
  have hdiag : IsSelfAdjoint (Matrix.blockDiagonal' A) :=
    Matrix.isHermitian_blockDiagonal'_iff.mpr hA
  have hh := (diagonalHom (κ := κ)).map_cfc f A (by rwa [Pi.spectrum_eq])
    (by change Continuous (Matrix.blockDiagonal' (m' := κ) (n' := κ)); fun_prop)
    hself hdiag
  rw [cfc_map_pi (S := ℝ) (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint)
    f A hf hself hA] at hh
  exact hh.symm

end SchurEntropy.MultiBlock
