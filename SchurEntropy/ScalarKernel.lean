import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The scalar kernel in the joint-convexity Hessian

This file proves the scalar logarithmic-mean bound and the positive-semidefinite
2-by-2 coefficient certificate used by `ScalarHessian`. The full matrix
calculation and joint convexity theorem are proved in `ScalarHessian` and
`ScalarConvexity`.
-/

noncomputable section
namespace SchurEntropy.ScalarKernel

/-- The inverse logarithmic mean, with its continuous value on the diagonal. -/
def inverseLogMean (a b : ℝ) : ℝ :=
  if a = b then a⁻¹ else (Real.log a - Real.log b) / (a - b)

/-- An elementary hyperbolic-function form of logarithmic mean ≥ geometric mean. -/
theorem two_log_le_sub_inv {t : ℝ} (ht : 1 ≤ t) :
    2 * Real.log t ≤ t - t⁻¹ := by
  have htpos : 0 < t := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg ht)
  rw [Real.sinh_eq, Real.exp_log htpos, Real.exp_neg, Real.exp_log htpos] at h
  linarith

/-- The logarithmic-mean inequality before dividing by `a-b`. -/
theorem sqrt_mul_log_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    Real.sqrt (a * b) * (Real.log a - Real.log b) ≤ a - b := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsba : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hba
  have h := two_log_le_sub_inv ((one_le_div hsb).mpr hsba)
  rw [Real.log_div hsa.ne' hsb.ne', Real.log_sqrt ha.le, Real.log_sqrt hb.le,
    inv_div] at h
  have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hsa.le hsb.le)
  have he : Real.sqrt a * Real.sqrt b *
      (Real.sqrt a / Real.sqrt b - Real.sqrt b / Real.sqrt a) = a - b := by
    field_simp
    nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  rw [he] at hm
  rw [Real.sqrt_mul ha.le]
  nlinarith

@[simp] theorem inverseLogMean_self {a : ℝ} : inverseLogMean a a = a⁻¹ := by
  simp [inverseLogMean]

theorem inverseLogMean_symm (a b : ℝ) : inverseLogMean a b = inverseLogMean b a := by
  by_cases hab : a = b
  · subst b; rfl
  · simp only [inverseLogMean, hab, Ne.symm hab, ↓reduceIte]
    rw [show Real.log b - Real.log a = -(Real.log a - Real.log b) by ring,
      show b - a = -(a - b) by ring, neg_div_neg_eq]

theorem inverseLogMean_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ inverseLogMean a b := by
  by_cases hab : a = b
  · subst b; simp only [inverseLogMean_self]; positivity
  simp only [inverseLogMean, hab, ↓reduceIte]
  rcases le_total b a with hba | hab'
  · exact div_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba)) (sub_nonneg.mpr hba)
  · exact div_nonneg_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab'))
      (sub_nonpos.mpr hab')

/-- The inverse logarithmic mean is bounded above by the inverse geometric mean,
written without a reciprocal on the right. -/
theorem sqrt_mul_inverseLogMean_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * inverseLogMean a b ≤ 1 := by
  wlog hba : b ≤ a generalizing a b
  · have hab : a ≤ b := le_of_not_ge hba
    simpa [mul_comm a b, inverseLogMean_symm a b] using this hb ha hab
  by_cases hab : a = b
  · subst b
    simp [Real.sqrt_mul_self ha.le, ha.ne']
  have hlt : b < a := lt_of_le_of_ne hba (Ne.symm hab)
  simp only [inverseLogMean, hab, ↓reduceIte]
  rw [← mul_div_assoc]
  exact (div_le_one (sub_pos.mpr hlt)).mpr (sqrt_mul_log_sub_le ha hb hba)

/-- Explicit sum-of-squares certificate for the real quadratic form. -/
theorem quadratic_eq_squares (a s ell x y : ℝ) (hs : s ≠ 0) :
    (a - s^2 * ell) * x^2 + 2 * (1 - a * ell) * x * y
        + (a / s^2 - ell) * y^2 =
      ((a + s) * (1 - s * ell) / (2 * s^2)) * (s*x+y)^2
        + ((a - s) * (1 + s * ell) / (2 * s^2)) * (s*x-y)^2 := by
  field_simp
  ring

/-- The positivity certificate in variables suited to logarithmic means. -/
theorem quadratic_nonneg_of_geometric_bound {a s ell : ℝ}
    (hs : 0 < s) (hsa : s ≤ a) (hell : 0 ≤ ell) (hbound : s * ell ≤ 1)
    (x y : ℝ) :
    0 ≤ (a - s^2 * ell) * x^2 + 2 * (1 - a * ell) * x * y
        + (a / s^2 - ell) * y^2 := by
  rw [quadratic_eq_squares a s ell x y hs.ne']
  have hden : 0 ≤ 2 * s^2 := by positivity
  have hfirst : 0 ≤ (a+s) * (1-s*ell) / (2*s^2) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hden
  have hsecond : 0 ≤ (a-s) * (1+s*ell) / (2*s^2) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hsa) (by positivity)) hden
  exact add_nonneg (mul_nonneg hfirst (sq_nonneg _))
    (mul_nonneg hsecond (sq_nonneg _))

/-- The exact real 2-by-2 spectral coefficient in the entropy Hessian is PSD. -/
theorem logarithmic_kernel_quadratic_nonneg {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    0 ≤ ((a+b)/2 - a*b*inverseLogMean a b) * x^2
      + 2 * (1 - ((a+b)/2)*inverseLogMean a b) * x*y
      + (((a+b)/2)/(a*b) - inverseLogMean a b) * y^2 := by
  have hp : 0 < a*b := mul_pos ha hb
  have hs : 0 < Real.sqrt (a*b) := Real.sqrt_pos.mpr hp
  have hs_sq : (Real.sqrt (a*b))^2 = a*b := Real.sq_sqrt hp.le
  have hmean : Real.sqrt (a*b) ≤ (a+b)/2 := by
    nlinarith [sq_nonneg (a-b)]
  have h := quadratic_nonneg_of_geometric_bound hs hmean
    (inverseLogMean_nonneg ha hb) (sqrt_mul_inverseLogMean_le_one ha hb) x y
  simpa only [hs_sq] using h

/-- The same spectral certificate for complex matrix entries. -/
theorem logarithmic_kernel_complex_nonneg {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : ℂ) :
    0 ≤ ((a+b)/2 - a*b*inverseLogMean a b) * Complex.normSq x
      + 2 * (1 - ((a+b)/2)*inverseLogMean a b) * (star x*y).re
      + (((a+b)/2)/(a*b) - inverseLogMean a b) * Complex.normSq y := by
  have hre := logarithmic_kernel_quadratic_nonneg ha hb x.re y.re
  have him := logarithmic_kernel_quadratic_nonneg ha hb x.im y.im
  have hid :
      ((a+b)/2 - a*b*inverseLogMean a b) * Complex.normSq x
        + 2 * (1 - ((a+b)/2)*inverseLogMean a b) * (star x*y).re
        + (((a+b)/2)/(a*b) - inverseLogMean a b) * Complex.normSq y =
      (((a+b)/2 - a*b*inverseLogMean a b) * x.re^2
        + 2 * (1 - ((a+b)/2)*inverseLogMean a b) * x.re*y.re
        + (((a+b)/2)/(a*b) - inverseLogMean a b) * y.re^2) +
      (((a+b)/2 - a*b*inverseLogMean a b) * x.im^2
        + 2 * (1 - ((a+b)/2)*inverseLogMean a b) * x.im*y.im
        + (((a+b)/2)/(a*b) - inverseLogMean a b) * y.im^2) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [hid]
  exact add_nonneg hre him


end SchurEntropy.ScalarKernel
