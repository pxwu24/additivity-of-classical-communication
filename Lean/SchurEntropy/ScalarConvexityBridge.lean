import SchurEntropy.ScalarConvexityCalculus
import QubitAdditivity.Imported.TensorEntropy

/-! Identification of the matrix deficit with its differentiable scalar path. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace SchurEntropy.ScalarConvexity
open QubitAdditivity

/-- Entropy of a real diagonal matrix, with the conversion to bits explicit. -/
theorem entropy_scalarDiagonal {m : ℕ} (r : Fin m → ℝ) :
    SchurEntropy.entropy (scalarDiagonal r) =
      (∑ i, Real.negMulLog (r i)) / Real.log 2 := by
  change SchurEntropy.entropy (HermitianMat.diagonal ℂ r).mat = _
  rw [entropy_eq_imported]
  change OpenAIEntropy.entropy (Matrix.diagonal (fun i => (r i : ℂ))) / _ = _
  rw [OpenAIEntropy.entropy_diagonal]

/-- The pinched scalar skeleton has diagonal entries `Cᵢᵢ rᵢ`. -/
theorem scalarSkeleton_diagonal {m : ℕ} (C : HermitianMat (Fin m) ℂ)
    (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) :
    Matrix.diagonal (scalarSkeleton C.mat r).diag =
      scalarDiagonal (fun i => (C.mat i i).re * r i) := by
  apply congrArg Matrix.diagonal
  funext i
  have hc : ((C.mat i i).re : ℂ) = C.mat i i :=
    Complex.conj_eq_iff_re.mp (C.H.apply i i)
  simp only [scalarSkeleton, scalarDiagonal, Matrix.diag_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Complex.ofReal_mul, hc]
  calc
    (Real.sqrt (r i) : ℂ) * C.mat i i * (Real.sqrt (r i) : ℂ) =
      C.mat i i * ((Real.sqrt (r i) : ℂ) ^ 2) := by ring
    _ = _ := by rw [← Complex.ofReal_pow, Real.sq_sqrt (hr i)]

/-- The actual scalar function in the paper is exactly the natural-logarithm
path used in the calculus proofs, divided by `log 2`. -/
theorem scalarFunction_eq_deficitPath {m : ℕ} (C : HermitianMat (Fin m) ℂ)
    (r y h k : Fin m → ℝ) (t : ℝ) (hr : ∀ i, 0 ≤ r i + t * h i) :
    scalarFunction C.mat (fun i => r i + t * h i) (fun i => y i + t * k i) =
      deficitPath C (fun i => (C.mat i i).re) r y h k t / Real.log 2 := by
  have hout : scalarSkeleton C.mat (fun i => r i+t*h i) +
      scalarDiagonal (fun i => y i+t*k i) = (outputPath C r y h k t).mat := by
    rw [outputPath_mat]
    rfl
  unfold scalarFunction scalarDeficit
  rw [hout, entropy_eq_imported, scalarSkeleton_diagonal C _ hr,
    entropy_scalarDiagonal, entropy_scalarDiagonal]
  simp only [deficitPath, Finset.sum_neg_distrib]
  ring

end SchurEntropy.ScalarConvexity
