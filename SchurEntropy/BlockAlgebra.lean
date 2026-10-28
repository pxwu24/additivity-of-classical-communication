/-
Adapted in part from KitaKen1/qubit-strong-additivity,
lean/QubitAdditivity/BetaOperators.lean,
commit 90e61c463deb42067c109c46f048c6374dfc5945 (Apache-2.0).
The coordinate-inclusion and generator/compression arguments are adapted;
the declarations are specialized and reorganized for this block-entropy proof.
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/
import SchurEntropy.Definitions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Matrix-unit coordinates for an arbitrary finite block decomposition

The diagonal-block matrix units form an orthonormal subset of all matrix units.
The inclusion below realizes this fact as a rectangular matrix isometry.  The
compression of a commutator generator is the direct sum of its block generators;
adding a scalar to any block leaves that generator unchanged.

These are finite-dimensional algebraic results, independent of the analytic
entropy inequalities and of any existence or stationarity theorem.
-/

noncomputable section

open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace SchurEntropy.BlockAlgebra

section Coordinates

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A rectangular matrix selecting an injectively indexed set of coordinates. -/
def coordinateInclusion (e : κ ↪ ι) : Matrix ι κ ℂ :=
  (1 : Matrix ι ι ℂ).submatrix id e

omit [Fintype κ] [DecidableEq κ] in
/-- Coordinate compression is precisely extraction of the corresponding submatrix. -/
theorem coordinateInclusion_compression (e : κ ↪ ι) (A : Matrix ι ι ℂ) :
    (coordinateInclusion e)ᴴ * A * coordinateInclusion e = A.submatrix e e := by
  simp only [coordinateInclusion, conjTranspose_submatrix, conjTranspose_one]
  change (1 : Matrix ι ι ℂ).submatrix e (Equiv.refl ι) * A *
    (1 : Matrix ι ι ℂ).submatrix (Equiv.refl ι) e = _
  rw [one_submatrix_mul e (Equiv.refl ι), mul_submatrix_one (Equiv.refl ι) e]
  rfl

omit [Fintype κ] in
/-- The selected coordinate vectors are orthonormal. -/
theorem coordinateInclusion_isometry (e : κ ↪ ι) :
    (coordinateInclusion e)ᴴ * coordinateInclusion e = 1 := by
  have h := coordinateInclusion_compression e (1 : Matrix ι ι ℂ)
  simpa only [Matrix.mul_one, submatrix_one_embedding] using h

theorem coordinateInclusion_mulVec_injective (e : κ ↪ ι) :
    Function.Injective (coordinateInclusion e).mulVec := by
  intro x y h
  have h' := congrArg (fun z => (coordinateInclusion e)ᴴ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, coordinateInclusion_isometry,
    Matrix.one_mulVec] using h'

omit [DecidableEq κ] in
theorem coordinateInclusion_compression_posSemidef (e : κ ↪ ι)
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    ((coordinateInclusion e)ᴴ * A * coordinateInclusion e).PosSemidef :=
  hA.conjTranspose_mul_mul_same (coordinateInclusion e)

theorem coordinateInclusion_compression_posDef (e : κ ↪ ι)
    {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    ((coordinateInclusion e)ᴴ * A * coordinateInclusion e).PosDef :=
  hA.conjTranspose_mul_mul_same (coordinateInclusion_mulVec_injective e)

end Coordinates

/-- Row-major matrix coordinates for the commutator `X ↦ A * X - X * A`. -/
def generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  A ⊗ₖ (1 : Matrix ι ι ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ Aᵀ

theorem generator_add_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (c : ℂ) :
    generator (A + c • (1 : Matrix ι ι ℂ)) = generator A := by
  simp only [generator, add_kronecker, transpose_add, transpose_smul,
    transpose_one, kronecker_add, smul_kronecker, kronecker_smul]
  abel

theorem generator_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : (generator A).IsHermitian := by
  unfold Matrix.IsHermitian generator
  simp only [conjTranspose_sub, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_transpose_eq_transpose_conjTranspose, hA.eq]

variable {m : ℕ} (n : Fin m → ℕ)

/-- Matrix-unit coordinates retained by the block pinching map. -/
abbrev DiagonalUnitIndex := (i : Fin m) × (Fin (n i) × Fin (n i))

/-- The injection of diagonal-block matrix units into all matrix units. -/
def diagonalUnitEmbedding : DiagonalUnitIndex n ↪ (BlockIndex n × BlockIndex n) where
  toFun a := (⟨a.1, a.2.1⟩, ⟨a.1, a.2.2⟩)
  inj' := by
    rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
    have hij : i = j := congrArg (fun z => z.1.1) h
    subst j
    simpa only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

@[simp] theorem diagonalUnitEmbedding_apply (a : DiagonalUnitIndex n) :
    diagonalUnitEmbedding n a = (⟨a.1, a.2.1⟩, ⟨a.1, a.2.2⟩) := rfl

/-- Isometric inclusion of the block-diagonal Hilbert--Schmidt coordinates. -/
def blockInclusion :
    Matrix (BlockIndex n × BlockIndex n) (DiagonalUnitIndex n) ℂ :=
  coordinateInclusion (diagonalUnitEmbedding n)

theorem blockInclusion_isometry : (blockInclusion n)ᴴ * blockInclusion n = 1 :=
  coordinateInclusion_isometry (diagonalUnitEmbedding n)

theorem blockInclusion_compression_posSemidef
    {A : Matrix (BlockIndex n × BlockIndex n) (BlockIndex n × BlockIndex n) ℂ}
    (hA : A.PosSemidef) :
    ((blockInclusion n)ᴴ * A * blockInclusion n).PosSemidef :=
  coordinateInclusion_compression_posSemidef (diagonalUnitEmbedding n) hA

theorem blockInclusion_compression_posDef
    {A : Matrix (BlockIndex n × BlockIndex n) (BlockIndex n × BlockIndex n) ℂ}
    (hA : A.PosDef) :
    ((blockInclusion n)ᴴ * A * blockInclusion n).PosDef :=
  coordinateInclusion_compression_posDef (diagonalUnitEmbedding n) hA

/-- The matrix acting on one diagonal block. -/
def diagonalBlock (H : BlockMatrix n) (i : Fin m) : Matrix (Fin (n i)) (Fin (n i)) ℂ :=
  H.submatrix (fun a => ⟨i, a⟩) (fun a => ⟨i, a⟩)

/-- The direct sum of the individual commutator generators. -/
def blockGenerator (W : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    Matrix (DiagonalUnitIndex n) (DiagonalUnitIndex n) ℂ :=
  Matrix.blockDiagonal' (fun i => generator (W i))

/-- Compressing the full commutator discards interactions between distinct blocks. -/
theorem generator_compression (H : BlockMatrix n) :
    (blockInclusion n)ᴴ * generator H * blockInclusion n =
      blockGenerator n (diagonalBlock n H) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext ⟨i, a, b⟩ ⟨j, c, d⟩
  by_cases hij : i = j
  · subst j
    simp [generator, blockGenerator, diagonalBlock, Matrix.one_apply]
  · simp [generator, blockGenerator, diagonalBlock,
      Matrix.blockDiagonal'_apply_ne, hij]

/-- Scalar multipliers on individual blocks cancel from the commutator.
This is the algebraic consequence of a blockwise logarithmic stationarity
equation; the existence of a stationary point is a separate analytic question. -/
theorem generator_compression_of_stationarity (H : BlockMatrix n)
    (W : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ) (μ : Fin m → ℂ)
    (h : ∀ i, W i = diagonalBlock n H i + μ i • 1) :
    (blockInclusion n)ᴴ * generator H * blockInclusion n = blockGenerator n W := by
  rw [generator_compression]
  unfold blockGenerator
  apply congrArg Matrix.blockDiagonal'
  funext i
  rw [h i, generator_add_scalar]

end SchurEntropy.BlockAlgebra
