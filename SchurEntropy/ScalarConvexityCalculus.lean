import SchurEntropy.Definitions
import QubitAdditivity.BetaLog
import QubitAdditivity.BetaDualDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Deriv

/-!
# Differential calculus for the scalar entropy deficit

These lemmas differentiate actual spectral matrix entropy. The logarithmic
Fréchet derivative is the resolvent integral proved in `BetaLog`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix Filter Set
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.ScalarConvexity
open QubitAdditivity

variable {n : Type*} [Fintype n] [DecidableEq n]

@[reducible] local instance mNorm : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace : NormedSpace ℝ (Matrix n n ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix n n ℂ)
@[reducible] local instance mTop : TopologicalSpace (Matrix n n ℂ) :=
  mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd : AddCommGroup (Matrix n n ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule : Module ℝ (Matrix n n ℂ) := mSpace.toModule
@[reducible] local instance hTop : TopologicalSpace (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd : AddCommGroup (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule : Module ℝ (HermitianMat n ℂ) :=
  HermitianMat.instNormedSpace.toModule

/-- The imported natural-logarithm entropy agrees with our entropy in bits. -/
theorem entropy_eq_imported (A : HermitianMat n ℂ) :
    SchurEntropy.entropy A.mat = OpenAIEntropy.entropy A.mat / Real.log 2 := by
  rw [SchurEntropy.entropy_eq_sum_eigenvalues A.H, OpenAIEntropy.entropy_eq_sum A.H]

/-- First variation of entropy along a differentiable Hermitian matrix path. -/
theorem hasDerivAt_entropy_path {B : ℝ → HermitianMat n ℂ} {t : ℝ}
    {H : HermitianMat n ℂ} (hB : (B t).mat.PosDef) (hB' : HasDerivAt B H t) :
    HasDerivAt (fun s => OpenAIEntropy.entropy (B s).mat)
      (-(H.mat * (BetaPowers.logarithm (B t).mat + 1)).trace.re) t := by
  convert! (BetaLog.hasFDerivAt_entropy hB).comp_hasDerivAt t hB' using 1
  exact (BetaLog.entropyGradient_apply _ _).symm

/-- First variation in bits, with its normalization explicit. -/
theorem hasDerivAt_entropy_bits_path {B : ℝ → HermitianMat n ℂ} {t : ℝ}
    {H : HermitianMat n ℂ} (hB : (B t).mat.PosDef) (hB' : HasDerivAt B H t) :
    HasDerivAt (fun s => SchurEntropy.entropy (B s).mat)
      (-(H.mat * (BetaPowers.logarithm (B t).mat + 1)).trace.re / Real.log 2) t := by
  simpa only [entropy_eq_imported] using (hasDerivAt_entropy_path hB hB').div_const (Real.log 2)

/-- The second variation, expressed without assuming that the path is affine. -/
theorem hasDerivAt_entropy_gradient_path
    {B H : ℝ → HermitianMat n ℂ} {t : ℝ} {K : HermitianMat n ℂ}
    (hB : (B t).mat.PosDef) (hB' : HasDerivAt B (H t) t)
    (hH' : HasDerivAt H K t) :
    HasDerivAt
      (fun s => -((H s).mat * (BetaPowers.logarithm (B s).mat + 1)).trace.re)
      (-((K.mat * (BetaPowers.logarithm (B t).mat + 1)).trace.re) -
        ((H t).mat * BetaLog.logDeriv (B t).mat (H t)).trace.re) t := by
  have hh := (BetaLog.inclusion (n := n)).hasFDerivAt.comp_hasDerivAt t hH'
  have hl := ((BetaLog.hasFDerivAt_logarithm hB).comp_hasDerivAt t hB').add_const
    (1 : Matrix n n ℂ)
  have hm := hh.mul hl
  have ht := (BetaLog.traceRe (n := n)).hasFDerivAt.comp_hasDerivAt t hm
  convert ht.neg using 1
  · ext s
    rfl
  · simp only [BetaLog.inclusion_apply, BetaLog.traceRe_apply, Matrix.trace_add,
      Complex.add_re, neg_add_rev, Function.comp_apply]
    ring

/-- The diagonal embedding as a continuous real linear map. -/
def diagonalLM : (n → ℝ) →ₗ[ℝ] HermitianMat n ℂ where
  toFun := HermitianMat.diagonal ℂ
  map_add' := HermitianMat.diagonal_add
  map_smul' c f := HermitianMat.diagonal_mul f c

def diagonalCLM : (n → ℝ) →L[ℝ] HermitianMat n ℂ :=
  diagonalLM.toContinuousLinearMap

@[simp] theorem diagonalCLM_apply (r : n → ℝ) :
    diagonalCLM r = HermitianMat.diagonal ℂ r := rfl

/-- Derivative of one square-root weight along an affine path. -/
theorem hasDerivAt_sqrt_affine (r h t : ℝ) (hp : 0 < r + t * h) :
    HasDerivAt (fun s => Real.sqrt (r + s * h))
      (h / (2 * Real.sqrt (r + t * h))) t := by
  convert! (((hasDerivAt_id t).mul_const h).const_add r).sqrt (ne_of_gt hp) using 1
  simp only [id_eq, one_mul]

/-- Second derivative of one square-root weight along an affine path. -/
theorem hasDerivAt_sqrt_affine_derivative (r h t : ℝ) (hp : 0 < r + t * h) :
    HasDerivAt (fun s => h / (2 * Real.sqrt (r + s * h)))
      (-(h ^ 2) / (4 * Real.sqrt (r + t * h) ^ 3)) t := by
  have hs : Real.sqrt (r + t * h) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  convert (hasDerivAt_const t h).div
    ((hasDerivAt_sqrt_affine r h t hp).const_mul 2) (mul_ne_zero (by norm_num) hs) using 1
  field_simp
  ring

/-- Diagonal square-root path, with all coordinates kept explicit. -/
def sqrtPath (r h : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => Real.sqrt (r i + t * h i))

def sqrtPath₁ (r h : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => h i / (2 * Real.sqrt (r i + t * h i)))

def sqrtPath₂ (r h : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => -(h i ^ 2) / (4 * Real.sqrt (r i + t * h i) ^ 3))

theorem hasDerivAt_sqrtPath (r h : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    HasDerivAt (sqrtPath r h) (sqrtPath₁ r h t) t := by
  have hv : HasDerivAt (fun s i => Real.sqrt (r i + s * h i))
      (fun i => h i / (2 * Real.sqrt (r i + t * h i))) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_sqrt_affine (r i) (h i) t (hp i))
  convert! (diagonalCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hv using 1

theorem hasDerivAt_sqrtPath₁ (r h : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    HasDerivAt (sqrtPath₁ r h) (sqrtPath₂ r h t) t := by
  have hv : HasDerivAt (fun s i => h i / (2 * Real.sqrt (r i + s * h i)))
      (fun i => -(h i ^ 2) / (4 * Real.sqrt (r i + t * h i) ^ 3)) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_sqrt_affine_derivative (r i) (h i) t (hp i))
  convert! (diagonalCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hv using 1

/-- The output matrix along an affine path in the nonnegative weights. -/
def outputPath (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ) :
    HermitianMat n ℂ :=
  BetaDualDerivative.hermitianPart
    ((sqrtPath r h t).mat * C.mat * (sqrtPath r h t).mat +
      (HermitianMat.diagonal ℂ (fun i => y i + t * k i)).mat)

def outputPath₁ (C : HermitianMat n ℂ) (r h k : n → ℝ) (t : ℝ) :
    HermitianMat n ℂ :=
  BetaDualDerivative.hermitianPart
    ((sqrtPath₁ r h t).mat * C.mat * (sqrtPath r h t).mat +
      (sqrtPath r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (HermitianMat.diagonal ℂ k).mat)

def outputPath₂ (C : HermitianMat n ℂ) (r h : n → ℝ) (t : ℝ) :
    HermitianMat n ℂ :=
  BetaDualDerivative.hermitianPart
    ((sqrtPath₂ r h t).mat * C.mat * (sqrtPath r h t).mat +
      (sqrtPath₁ r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (sqrtPath₁ r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (sqrtPath r h t).mat * C.mat * (sqrtPath₂ r h t).mat)

/-- The projection in `outputPath` preserves its already Hermitian argument. -/
theorem outputPath_mat (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ) :
    (outputPath C r y h k t).mat =
      (sqrtPath r h t).mat * C.mat * (sqrtPath r h t).mat +
        (HermitianMat.diagonal ℂ (fun i => y i + t * k i)).mat := by
  have hc : ((sqrtPath r h t).mat * C.mat * (sqrtPath r h t).mat).IsHermitian := by
    simpa only [(sqrtPath r h t).H.eq] using
      Matrix.isHermitian_mul_mul_conjTranspose (sqrtPath r h t).mat C.H
  have hh := hc.add (HermitianMat.diagonal ℂ (fun i => y i + t * k i)).H
  exact congrArg HermitianMat.mat (BetaDualDerivative.hermitianPart_mat ⟨_, hh⟩)

/-- The actual first derivative of the output matrix. -/
theorem hasDerivAt_outputPath (C : HermitianMat n ℂ) (r y h k : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    HasDerivAt (outputPath C r y h k) (outputPath₁ C r h k t) t := by
  have hd := (BetaLog.inclusion (n := n)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_sqrtPath r h t hp)
  have hv : HasDerivAt (fun s i => y i + s * k i) k t := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using (((hasDerivAt_id t).mul_const (k i)).const_add (y i))
  have hy := (diagonalCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hv
  have hym := (BetaLog.inclusion (n := n)).hasFDerivAt.comp_hasDerivAt t hy
  have hm := ((hd.mul_const C.mat).mul hd).add hym
  convert! (BetaDualDerivative.hermitianPart (k := n)).hasFDerivAt.comp_hasDerivAt t hm using 1

/-- The actual second derivative of the output matrix. -/
theorem hasDerivAt_outputPath₁ (C : HermitianMat n ℂ) (r h k : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    HasDerivAt (outputPath₁ C r h k) (outputPath₂ C r h t) t := by
  have hd := (BetaLog.inclusion (n := n)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_sqrtPath r h t hp)
  have hd₁ := (BetaLog.inclusion (n := n)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_sqrtPath₁ r h t hp)
  have hm := (((hd₁.mul_const C.mat).mul hd).add ((hd.mul_const C.mat).mul hd₁)).add_const
    (HermitianMat.diagonal ℂ k).mat
  convert! (BetaDualDerivative.hermitianPart (k := n)).hasFDerivAt.comp_hasDerivAt t hm using 1
  dsimp only [outputPath₂, Function.comp_apply, BetaLog.inclusion_apply]
  congr 1
  noncomm_ring

theorem outputPath₁_mat (C : HermitianMat n ℂ) (r h k : n → ℝ) (t : ℝ) :
    (outputPath₁ C r h k t).mat =
      (sqrtPath₁ r h t).mat * C.mat * (sqrtPath r h t).mat +
      (sqrtPath r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (HermitianMat.diagonal ℂ k).mat := by
  apply congrArg HermitianMat.mat (BetaDualDerivative.hermitianPart_mat ⟨_, ?_⟩)
  change _ᴴ = _
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, C.H.eq,
    (sqrtPath r h t).H.eq, (sqrtPath₁ r h t).H.eq,
    (HermitianMat.diagonal ℂ k).H.eq]
  noncomm_ring

theorem outputPath₂_mat (C : HermitianMat n ℂ) (r h : n → ℝ) (t : ℝ) :
    (outputPath₂ C r h t).mat =
      (sqrtPath₂ r h t).mat * C.mat * (sqrtPath r h t).mat +
      (sqrtPath₁ r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (sqrtPath₁ r h t).mat * C.mat * (sqrtPath₁ r h t).mat +
      (sqrtPath r h t).mat * C.mat * (sqrtPath₂ r h t).mat := by
  apply congrArg HermitianMat.mat (BetaDualDerivative.hermitianPart_mat ⟨_, ?_⟩)
  change _ᴴ = _
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, C.H.eq,
    (sqrtPath r h t).H.eq, (sqrtPath₁ r h t).H.eq, (sqrtPath₂ r h t).H.eq]
  noncomm_ring

/-- Logarithmic velocity of the diagonal weights. -/
def velocity (r h : n → ℝ) (t : ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => h i / (r i + t * h i))

lemma sqrt_velocity_identity (r h : ℝ) (hr : 0 < r) :
    h / (2 * Real.sqrt r) = (1 / 2 : ℝ) * (h / r) * Real.sqrt r := by
  have hs := (Real.sqrt_pos.2 hr).ne'
  conv_rhs => rw [← Real.sq_sqrt hr.le]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp

lemma sqrt_acceleration_identity (r h : ℝ) (hr : 0 < r) :
    -(h ^ 2) / (4 * Real.sqrt r ^ 3) =
      (-1 / 4 : ℝ) * ((h / r) * (h / r)) * Real.sqrt r := by
  have hs := (Real.sqrt_pos.2 hr).ne'
  conv_rhs => rw [← Real.sq_sqrt hr.le]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg _)]
  field_simp

theorem sqrtPath₁_eq_velocity (r h : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    (sqrtPath₁ r h t).mat =
      (1 / 2 : ℝ) • ((velocity r h t).mat * (sqrtPath r h t).mat) := by
  simp only [sqrtPath₁, sqrtPath, velocity, HermitianMat.diagonal_mat,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [sqrt_velocity_identity (r i + t * h i) (h i) (hp i)]
  push_cast
  ring

theorem sqrtPath₂_eq_velocity (r h : n → ℝ) (t : ℝ)
    (hp : ∀ i, 0 < r i + t * h i) :
    (sqrtPath₂ r h t).mat =
      (-1 / 4 : ℝ) • ((velocity r h t).mat * (velocity r h t).mat *
        (sqrtPath r h t).mat) := by
  simp only [sqrtPath₂, sqrtPath, velocity, HermitianMat.diagonal_mat,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [sqrt_acceleration_identity (r i + t * h i) (h i) (hp i)]
  push_cast
  ring

/-- Classical entropy variation, including a vanishing coefficient. -/
theorem hasDerivAt_neg_entropy_affine (c r h t : ℝ)
    (hc : 0 ≤ c) (hr : 0 < r + t * h) :
    HasDerivAt (fun s => -Real.negMulLog (c * (r + s * h)))
      (c * h * (Real.log (c * (r + t * h)) + 1)) t := by
  rcases eq_or_lt_of_le hc with hc | hc
  · subst c
    simpa using hasDerivAt_const t (0 : ℝ)
  · have hf : HasDerivAt (fun s => c * (r + s * h)) (c * h) t := by
      convert (((hasDerivAt_id t).mul_const h).const_add r).const_mul c using 1 <;> simp
    convert! ((Real.hasDerivAt_negMulLog (mul_pos hc hr).ne').comp t hf).neg using 1
    ring

theorem hasDerivAt_neg_entropy_affine_derivative (c r h t : ℝ)
    (hc : 0 ≤ c) (hr : 0 < r + t * h) :
    HasDerivAt (fun s => c * h * (Real.log (c * (r + s * h)) + 1))
      (c * h ^ 2 / (r + t * h)) t := by
  rcases eq_or_lt_of_le hc with hc | hc
  · subst c
    simpa using hasDerivAt_const t (0 : ℝ)
  · have hf : HasDerivAt (fun s => c * (r + s * h)) (c * h) t := by
      convert (((hasDerivAt_id t).mul_const h).const_add r).const_mul c using 1 <;> simp
    convert ((hf.log (mul_pos hc hr).ne').add_const 1).const_mul (c * h) using 1
    field_simp

/-- Natural-logarithm deficit along an affine path in the weights. -/
def deficitPath (C : HermitianMat n ℂ) (c r y h k : n → ℝ) (t : ℝ) : ℝ :=
  OpenAIEntropy.entropy (outputPath C r y h k t).mat +
    ∑ i, -Real.negMulLog (c i * (r i + t * h i)) +
    ∑ i, -Real.negMulLog (y i + t * k i)

def deficitPath₁ (C : HermitianMat n ℂ) (c r y h k : n → ℝ) (t : ℝ) : ℝ :=
  -((outputPath₁ C r h k t).mat *
    (BetaPowers.logarithm (outputPath C r y h k t).mat + 1)).trace.re +
    ∑ i, c i * h i * (Real.log (c i * (r i + t * h i)) + 1) +
    ∑ i, k i * (Real.log (y i + t * k i) + 1)

def deficitPath₂ (C : HermitianMat n ℂ) (c r y h k : n → ℝ) (t : ℝ) : ℝ :=
  -((outputPath₂ C r h t).mat *
    (BetaPowers.logarithm (outputPath C r y h k t).mat + 1)).trace.re -
    ((outputPath₁ C r h k t).mat * BetaLog.logDeriv
      (outputPath C r y h k t).mat (outputPath₁ C r h k t)).trace.re +
    ∑ i, c i * h i ^ 2 / (r i + t * h i) +
    ∑ i, k i ^ 2 / (y i + t * k i)

theorem hasDerivAt_deficitPath (C : HermitianMat n ℂ) (c r y h k : n → ℝ) (t : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hr : ∀ i, 0 < r i + t * h i)
    (hy : ∀ i, 0 < y i + t * k i)
    (hB : (outputPath C r y h k t).mat.PosDef) :
    HasDerivAt (deficitPath C c r y h k) (deficitPath₁ C c r y h k t) t := by
  have hb := hasDerivAt_entropy_path hB (hasDerivAt_outputPath C r y h k t hr)
  have hr' := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hasDerivAt_neg_entropy_affine (c i) (r i) (h i) t (hc i) (hr i))
  have hy' := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hasDerivAt_neg_entropy_affine 1 (y i) (k i) t (by norm_num) (hy i))
  convert! (hb.add hr').add hy' using 1
  · funext s
    simp [deficitPath]
  · simp [deficitPath₁]

theorem hasDerivAt_deficitPath₁ (C : HermitianMat n ℂ) (c r y h k : n → ℝ) (t : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hr : ∀ i, 0 < r i + t * h i)
    (hy : ∀ i, 0 < y i + t * k i)
    (hB : (outputPath C r y h k t).mat.PosDef) :
    HasDerivAt (deficitPath₁ C c r y h k) (deficitPath₂ C c r y h k t) t := by
  have hb := hasDerivAt_entropy_gradient_path hB
    (hasDerivAt_outputPath C r y h k t hr) (hasDerivAt_outputPath₁ C r h k t hr)
  have hr' := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hasDerivAt_neg_entropy_affine_derivative (c i) (r i) (h i) t (hc i) (hr i))
  have hy' := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    hasDerivAt_neg_entropy_affine_derivative 1 (y i) (k i) t (by norm_num) (hy i))
  convert! (hb.add hr').add hy' using 1
  · funext s
    simp [deficitPath₁]
  · simp [deficitPath₂]

end SchurEntropy.ScalarConvexity
