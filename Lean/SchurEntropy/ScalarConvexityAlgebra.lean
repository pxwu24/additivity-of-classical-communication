import SchurEntropy.ScalarConvexityCalculus
import SchurEntropy.ScalarHessian
import QubitAdditivity.Imported.TensorEntropy

/-! Algebraic identities identifying the entropy path Hessian with the
positive spectral quadratic form. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix Filter Set
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.ScalarConvexity
open QubitAdditivity

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] mNorm mSpace mTop mAdd mModule hTop hAdd hModule

def doubleCommutator (X B : Matrix n n ℂ) : Matrix n n ℂ :=
  X * (X * B - B * X) - (X * B - B * X) * X

def noisePath (y k : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => y i + t * k i)

def residualVelocity (r y h k : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => k i - (y i + t * k i) * (h i / (r i + t * h i)))

/-- Rewriting the first derivative as the symmetric velocity plus the
residual diagonal perturbation. -/
theorem outputPath₁_eq_tangent (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    (outputPath₁ C r h k t).mat =
      (1 / 2 : ℝ) • ((velocity r h t).mat * (outputPath C r y h k t).mat +
        (outputPath C r y h k t).mat * (velocity r h t).mat) +
        (residualVelocity r y h k t).mat := by
  rw [outputPath₁_mat, sqrtPath₁_eq_velocity r h t hp, outputPath_mat]
  ext i j
  simp only [velocity, sqrtPath, residualVelocity, HermitianMat.diagonal_mat,
    smul_mul_assoc, mul_smul_comm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    push_cast
    ring
  · simp only [Matrix.diagonal_apply, ite_eq_right hij]
    push_cast
    ring

/-- The second output derivative is the negative double commutator. -/
theorem outputPath₂_eq_doubleComm (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    (outputPath₂ C r h t).mat =
      (-1 / 4 : ℝ) • doubleCommutator (velocity r h t).mat
        (outputPath C r y h k t).mat := by
  rw [outputPath₂_mat, sqrtPath₁_eq_velocity r h t hp,
    sqrtPath₂_eq_velocity r h t hp, outputPath_mat]
  ext i j
  simp only [doubleCommutator, velocity, sqrtPath,
    HermitianMat.diagonal_mat, smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Complex.real_smul]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    push_cast
    ring
  · simp only [Matrix.diagonal_apply, ite_eq_right hij]
    push_cast
    ring

omit [Fintype n] in
theorem noisePath_posDef (y k : n → ℝ) (t : ℝ)
    (hy : ∀ i, 0 < y i + t * k i) : (noisePath y k t).mat.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  exact RCLike.ofReal_pos.mpr (hy i)

theorem outputPath_sub_noise_posSemidef (C : HermitianMat n ℂ)
    (hC : C.mat.PosSemidef) (r y h k : n → ℝ) (t : ℝ) :
    ((outputPath C r y h k t).mat - (noisePath y k t).mat).PosSemidef := by
  rw [outputPath_mat]
  simp only [noisePath, add_sub_cancel_right]
  simpa only [(sqrtPath r h t).H.eq] using
    hC.mul_mul_conjTranspose_same (sqrtPath r h t).mat

theorem outputPath_posDef (C : HermitianMat n ℂ) (hC : C.mat.PosSemidef)
    (r y h k : n → ℝ) (t : ℝ) (hy : ∀ i, 0 < y i + t * k i) :
    (outputPath C r y h k t).mat.PosDef := by
  have hh := Matrix.PosDef.posSemidef_add
    (outputPath_sub_noise_posSemidef C hC r y h k t) (noisePath_posDef y k t hy)
  simpa only [sub_add_cancel] using hh

omit [DecidableEq n] in
theorem trace_doubleCommutator (X B : Matrix n n ℂ) :
    (doubleCommutator X B).trace = 0 := by
  rw [doubleCommutator, Matrix.trace_sub, Matrix.trace_mul_comm X]
  simp

theorem entropy_acceleration_eq (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ)
    (hr : ∀ i, 0 < r i + t * h i) :
    -((outputPath₂ C r h t).mat *
      (BetaPowers.logarithm (outputPath C r y h k t).mat + 1)).trace.re =
      ((doubleCommutator (velocity r h t).mat (outputPath C r y h k t).mat) *
        BetaPowers.logarithm (outputPath C r y h k t).mat).trace.re / 4 := by
  rw [outputPath₂_eq_doubleComm C r y h k t hr]
  simp only [smul_mul_assoc, Matrix.mul_add, Matrix.mul_one, Matrix.trace_smul,
    Matrix.trace_add, trace_doubleCommutator, add_zero, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem noisePath_inv (y k : n → ℝ) (t : ℝ) (hy : ∀ i, 0 < y i + t * k i) :
    (noisePath y k t).mat⁻¹ =
      (HermitianMat.diagonal ℂ (fun i => (y i + t * k i)⁻¹)).mat := by
  apply Matrix.inv_eq_right_inv
  simp only [noisePath, HermitianMat.diagonal_mat, Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one (n := n) (α := ℂ) using 1
  congr 1
  funext i
  change ((y i + t * k i : ℝ) : ℂ) * (((y i + t * k i)⁻¹ : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hy i).ne']
  rfl

/-- The diagonal scalar curvature is precisely the matrix quadratic term
used by the spectral logarithmic-mean estimate. -/
theorem classical_curvature_eq (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ)
    (hr : ∀ i, 0 < r i + t * h i) (hy : ∀ i, 0 < y i + t * k i) :
    (∑ i, (C.mat i i).re * h i ^ 2 / (r i + t * h i)) +
      (∑ i, k i ^ 2 / (y i + t * k i)) =
    ((velocity r h t).mat * (velocity r h t).mat * (outputPath C r y h k t).mat).trace.re +
      2 * ((velocity r h t).mat * (residualVelocity r y h k t).mat).trace.re +
      ((residualVelocity r y h k t).mat * (residualVelocity r y h k t).mat *
        (noisePath y k t).mat⁻¹).trace.re := by
  rw [outputPath_mat, noisePath_inv y k t hy]
  simp only [velocity, sqrtPath, residualVelocity, HermitianMat.diagonal_mat,
    Matrix.diagonal_mul_diagonal, Matrix.trace, Matrix.diag_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.diagonal_apply_eq, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [RCLike.ofReal, Algebra.cast, Complex.coe_algebraMap,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs := Real.sq_sqrt (hr i).le
  have hri := (hr i).ne'
  have hyi := (hy i).ne'
  have hid : ∀ a b c d s : ℝ, a ≠ 0 → b ≠ 0 → s ^ 2 = a →
      c * d ^ 2 / a + (k i) ^ 2 / b =
        (d / a * (d / a)) * (s * c * s + b) +
        2 * (d / a * (k i - b * (d / a))) +
        ((k i - b * (d / a)) * (k i - b * (d / a))) * b⁻¹ := by
    intro a b c d s ha hb hs
    have hsc : s * c * s = c * a := by calc
      _ = c * s ^ 2 := by ring
      _ = c * a := by rw [hs]
    rw [hsc]
    field_simp
    ring
  exact hid _ _ _ _ _ hri hyi hs

/-- Nonnegative second variation of the actual scalar entropy deficit. -/
theorem deficitPath₂_nonneg (C : HermitianMat n ℂ) (hC : C.mat.PosSemidef)
    (r y h k : n → ℝ) (t : ℝ)
    (hr : ∀ i, 0 < r i + t * h i) (hy : ∀ i, 0 < y i + t * k i) :
    0 ≤ deficitPath₂ C (fun i => (C.mat i i).re) r y h k t := by
  have hB := outputPath_posDef C hC r y h k t hy
  have ht : ScalarHessian.tangent (outputPath C r y h k t).mat
      (velocity r h t).mat (residualVelocity r y h k t).mat =
      (outputPath₁ C r h k t).mat :=
    (outputPath₁_eq_tangent C r y h k t hr).symm
  have he : (⟨ScalarHessian.tangent (outputPath C r y h k t).mat
      (velocity r h t).mat (residualVelocity r y h k t).mat,
      ScalarHessian.tangent_isHermitian _ _ _ hB.1
        (velocity r h t).H (residualVelocity r y h k t).H⟩ : HermitianMat n ℂ) =
      outputPath₁ C r h k t := HermitianMat.ext ht
  have hh := ScalarHessian.hessian_nonneg (outputPath C r y h k t).mat
    (noisePath y k t).mat (velocity r h t).mat (residualVelocity r y h k t).mat
    hB (noisePath_posDef y k t hy) (outputPath_sub_noise_posSemidef C hC r y h k t)
    (velocity r h t).H (residualVelocity r y h k t).H
  rw [he, ht] at hh
  have hc := classical_curvature_eq C r y h k t hr hy
  have ha := entropy_acceleration_eq C r y h k t hr
  unfold deficitPath₂
  change 0 ≤ _
  dsimp only [doubleCommutator, ScalarHessian.doubleComm] at hh ha
  linarith

end SchurEntropy.ScalarConvexity
