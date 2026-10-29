import SchurEntropy.Definitions
import SchurEntropy.ScalarKernel
import QubitAdditivity.BetaLogKM
import QubitAdditivity.BetaOrder

/-! Spectral trace algebra for the scalar entropy Hessian. -/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.ScalarHessian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diag (a : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal (fun i => (a i : ℂ))

def spectralLogDeriv (a : ι → ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (ScalarKernel.inverseLogMean (a i) (a j) : ℂ) * X i j

theorem trace_mul_eq_entry_sum (X Y : Matrix ι ι ℂ) (hX : X.IsHermitian) :
    (Matrix.trace (X * Y)).re = ∑ i, ∑ j, (star (X i j) * Y i j).re := by
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hx : X j i = star (X i j) := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      (congrFun (congrFun hX j) i).symm
  rw [hx, mul_comm]

theorem normSq_entry_symm (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (i j : ι) :
    Complex.normSq (X i j) = Complex.normSq (X j i) := by
  have hx : X j i = star (X i j) := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      (congrFun (congrFun hX j) i).symm
  rw [hx]
  simp

theorem sum_pair_average (f : ι → ι → ℝ) :
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, (f i j + f j i) / 2 := by
  have hswap : (∑ i, ∑ j, f j i) = ∑ i, ∑ j, f i j := Finset.sum_comm
  simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [hswap]
  ring

theorem normSq_real_mul_add (a : ℝ) (x y : ℂ) :
    Complex.normSq ((a : ℂ) * x + y) =
      a^2 * Complex.normSq x + 2*a*(star x*y).re + Complex.normSq y := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem trace_sq_mul_diag (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (a : ι → ℝ) :
    (Matrix.trace (X * X * diag a)).re =
      ∑ i, ∑ j, a j * Complex.normSq (X i j) := by
  rw [Matrix.mul_assoc, trace_mul_eq_entry_sum X (X * diag a) hX]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [diag, Matrix.mul_diagonal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

theorem trace_sq_mul_diag_average (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (a : ι → ℝ) :
    (Matrix.trace (X * X * diag a)).re =
      ∑ i, ∑ j, ((a i + a j) / 2) * Complex.normSq (X i j) := by
  rw [trace_sq_mul_diag X hX a, sum_pair_average]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← normSq_entry_symm X hX i j]
  ring

theorem trace_spectralLogDeriv (a : ι → ℝ) (K : Matrix ι ι ℂ)
    (hK : K.IsHermitian) :
    (Matrix.trace (K * spectralLogDeriv a K)).re =
      ∑ i, ∑ j, ScalarKernel.inverseLogMean (a i) (a j) *
        Complex.normSq (K i j) := by
  rw [trace_mul_eq_entry_sum K _ hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [spectralLogDeriv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

def doubleComm (X B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  X * (X * B - B * X) - (X * B - B * X) * X

theorem doubleComm_diag_entry (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (a : ι → ℝ) (i : ι) :
    doubleComm X (diag a) i i =
      ∑ j, (2 * (a i - a j) : ℝ) * (star (X i j) * X i j) := by
  have hc : X * diag a - diag a * X =
      (fun i j => X i j * (a j : ℂ) - (a i : ℂ) * X i j) := by
    ext i j
    simp [diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [doubleComm, hc]
  change (∑ j, X i j * (X j i * (a i : ℂ) - (a j : ℂ) * X j i)) -
      (∑ j, (X i j * (a j : ℂ) - (a i : ℂ) * X i j) * X j i) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hx : X j i = star (X i j) := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
      (congrFun (congrFun hX j) i).symm
  rw [hx]
  push_cast
  ring

theorem inverseLogMean_mul_sub (a b : ℝ) :
    ScalarKernel.inverseLogMean a b * (a-b) = Real.log a - Real.log b := by
  by_cases hab : a = b
  · subst b
    simp
  · simp only [ScalarKernel.inverseLogMean, hab, ↓reduceIte]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr hab)

theorem trace_doubleComm_diag (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (a : ι → ℝ) :
    (Matrix.trace (doubleComm X (diag a) * diag (fun i => Real.log (a i)))).re =
      ∑ i, ∑ j, 2 * (a i-a j) * Real.log (a i) * Complex.normSq (X i j) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  change (∑ i, (doubleComm X (diag a) *
    Matrix.diagonal (fun i => (Real.log (a i) : ℂ))) i i).re = _
  simp only [Matrix.mul_diagonal, doubleComm_diag_entry X hX a,
    Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem quarter_trace_doubleComm_diag (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (a : ι → ℝ) :
    (Matrix.trace (doubleComm X (diag a) * diag (fun i => Real.log (a i)))).re / 4 =
      ∑ i, ∑ j, ((a i-a j)^2 * ScalarKernel.inverseLogMean (a i) (a j) / 4) *
        Complex.normSq (X i j) := by
  rw [trace_doubleComm_diag X hX a, sum_pair_average]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← normSq_entry_symm X hX i j]
  calc
    _ = ((a i-a j) * (Real.log (a i)-Real.log (a j)) / 4) *
      Complex.normSq (X i j) := by ring
    _ = _ := by rw [← inverseLogMean_mul_sub (a i) (a j)]; ring

def tangent (B X E : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℝ) • (X * B + B * X) + E

theorem tangent_diag_entry (a : ι → ℝ) (X E : Matrix ι ι ℂ) (i j : ι) :
    tangent (diag a) X E i j = (((a i+a j)/2 : ℝ) : ℂ) * X i j + E i j := by
  simp only [tangent, Matrix.add_apply, Matrix.smul_apply, diag,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.real_smul]
  push_cast
  ring

theorem tangent_isHermitian (B X E : Matrix ι ι ℂ)
    (hB : B.IsHermitian) (hX : X.IsHermitian) (hE : E.IsHermitian) :
    (tangent B X E).IsHermitian := by
  change (tangent B X E).conjTranspose = tangent B X E
  simp only [tangent, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, hB.eq, hX.eq, hE.eq, star_trivial]
  rw [add_comm (B * X) (X * B)]

/-- The entropy Hessian's spectral trace quadratic form is nonnegative.
This is the diagonal-base matrix inequality, not just a scalar certificate. -/
theorem diagonal_hessian_nonneg (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (X E : Matrix ι ι ℂ) (hX : X.IsHermitian) (hE : E.IsHermitian) :
    0 ≤ (Matrix.trace (X * X * diag a)).re + 2 * (Matrix.trace (X * E)).re +
      (Matrix.trace (E * E * diag (fun i => (a i)⁻¹))).re -
      (Matrix.trace (tangent (diag a) X E * spectralLogDeriv a (tangent (diag a) X E))).re +
      (Matrix.trace (doubleComm X (diag a) * diag (fun i => Real.log (a i)))).re / 4 := by
  have hD : (diag a).IsHermitian := by
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hK := tangent_isHermitian (diag a) X E hD hX hE
  rw [trace_sq_mul_diag_average X hX, trace_mul_eq_entry_sum X E hX,
    trace_sq_mul_diag_average E hE, trace_spectralLogDeriv a _ hK,
    quarter_trace_doubleComm_diag X hX]
  simp_rw [tangent_diag_entry, normSq_real_mul_add]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  have hinv : ((a i)⁻¹ + (a j)⁻¹) / 2 = ((a i+a j)/2)/(a i*a j) := by
    field_simp [(ha i).ne', (ha j).ne']
    ring
  rw [hinv]
  convert ScalarKernel.logarithmic_kernel_complex_nonneg (ha i) (ha j) (X i j) (E i j) using 1 <;> ring

open QubitAdditivity
open BetaLogKM
open scoped Matrix.Norms.L2Operator

theorem inverseMean_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    BetaLogMean.inverseMean a b = ScalarKernel.inverseLogMean a b := by
  by_cases hab : a = b
  · subst b
    simp only [ScalarKernel.inverseLogMean, ↓reduceIte]
    have h := BetaLogMean.self_mul_inverseMean ha
    apply (mul_left_cancel₀ ha.ne')
    simpa [ha.ne'] using h
  · simp only [ScalarKernel.inverseLogMean, hab, ↓reduceIte]
    apply (eq_div_iff (sub_ne_zero.mpr hab)).mpr
    exact BetaLogMean.inverseMean_mul_sub ha hb

theorem trace_coordinates {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    (X : Matrix ι ι ℂ) : Matrix.trace (coordinates hB X) = Matrix.trace X := by
  simp only [coordinates, Unitary.conjStarAlgAut_symm_apply]
  rw [Matrix.trace_mul_cycle]
  simp

theorem coordinates_isHermitian {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) : (coordinates hB X).IsHermitian := by
  change star (coordinates hB X) = coordinates hB X
  simp only [coordinates, ← map_star, hX.star_eq]

theorem coordinates_self {B : Matrix ι ι ℂ} (hB : B.IsHermitian) :
    coordinates hB B = diag hB.eigenvalues := by
  calc
    coordinates hB B = coordinates hB
        (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hB.eigenvectorUnitary
          (diag hB.eigenvalues)) := congrArg (coordinates hB) hB.spectral_theorem
    _ = _ := (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hB.eigenvectorUnitary).symm_apply_apply _

theorem coordinates_inverse {B : Matrix ι ι ℂ} (hB : B.PosDef) :
    coordinates hB.1 B⁻¹ = diag (fun i => (hB.1.eigenvalues i)⁻¹) := by
  have h := coordinates_inverseSegment hB (t := 1) (by constructor <;> norm_num)
  simpa [BetaLog.inverseSegment, BetaLog.segment, diag] using h

theorem coordinates_tangent {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    (X E : Matrix ι ι ℂ) :
    coordinates hB (tangent B X E) =
      tangent (coordinates hB B) (coordinates hB X) (coordinates hB E) := by
  have hsmul (r : ℝ) (Z : Matrix ι ι ℂ) : coordinates hB (r • Z) = r • coordinates hB Z := by
    simp only [coordinates, Unitary.conjStarAlgAut_symm_apply, Matrix.mul_smul,
      Matrix.smul_mul]
  have hadd (Z W : Matrix ι ι ℂ) : coordinates hB (Z+W) = coordinates hB Z + coordinates hB W :=
    map_add _ _ _
  simp only [tangent, hadd, hsmul, coordinates_mul]

theorem coordinates_doubleComm {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    (X : Matrix ι ι ℂ) :
    coordinates hB (doubleComm X B) = doubleComm (coordinates hB X) (coordinates hB B) := by
  simp only [doubleComm, coordinates, map_sub, map_mul]

theorem coordinates_logDeriv_eq {B : Matrix ι ι ℂ} (hB : B.PosDef)
    (K : HermitianMat ι ℂ) :
    coordinates hB.1 (BetaLog.logDeriv B K) =
      spectralLogDeriv hB.1.eigenvalues (coordinates hB.1 K.mat) := by
  ext i j
  rw [coordinates_logDeriv hB K i j]
  rw [inverseMean_eq (hB.eigenvalues_pos i) (hB.eigenvalues_pos j)]
  rfl

/-- Spectral Hessian positivity at a general positive definite base. -/
theorem base_hessian_nonneg (B X E : Matrix ι ι ℂ)
    (hB : B.PosDef) (hX : X.IsHermitian) (hE : E.IsHermitian) :
    0 ≤ (Matrix.trace (X * X * B)).re + 2 * (Matrix.trace (X * E)).re +
      (Matrix.trace (E * E * B⁻¹)).re -
      (Matrix.trace (tangent B X E * BetaLog.logDeriv B
        ⟨tangent B X E, tangent_isHermitian B X E hB.1 hX hE⟩)).re +
      (Matrix.trace (doubleComm X B * BetaPowers.logarithm B)).re / 4 := by
  have hlog : coordinates hB.1 (BetaPowers.logarithm B) =
      diag (fun i => Real.log (hB.1.eigenvalues i)) := by
    convert! coordinates_cfc hB.1 Real.log using 1
  rw [← trace_coordinates hB.1 (X*X*B), ← trace_coordinates hB.1 (X*E),
    ← trace_coordinates hB.1 (E*E*B⁻¹),
    ← trace_coordinates hB.1 (tangent B X E * BetaLog.logDeriv B
      ⟨tangent B X E, tangent_isHermitian B X E hB.1 hX hE⟩),
    ← trace_coordinates hB.1 (doubleComm X B * BetaPowers.logarithm B)]
  have hder : coordinates hB.1 (BetaLog.logDeriv B
      ⟨tangent B X E, tangent_isHermitian B X E hB.1 hX hE⟩) =
      spectralLogDeriv hB.1.eigenvalues (coordinates hB.1 (tangent B X E)) := by
    convert! coordinates_logDeriv_eq hB
      ⟨tangent B X E, tangent_isHermitian B X E hB.1 hX hE⟩ using 1
  simp only [coordinates_mul, hder, coordinates_tangent, coordinates_doubleComm,
    coordinates_self, coordinates_inverse hB, hlog]
  exact diagonal_hessian_nonneg hB.1.eigenvalues hB.eigenvalues_pos
    (coordinates hB.1 X) (coordinates hB.1 E)
    (coordinates_isHermitian hB.1 hX) (coordinates_isHermitian hB.1 hE)

theorem trace_inverse_mono (B Y E : Matrix ι ι ℂ)
    (hB : B.PosDef) (hY : Y.PosDef) (hBY : (B-Y).PosSemidef)
    (hE : E.IsHermitian) :
    (Matrix.trace (E*E*B⁻¹)).re ≤ (Matrix.trace (E*E*Y⁻¹)).re := by
  have hi : (Y⁻¹-B⁻¹).PosSemidef := by
    simpa using BetaOrder.inverse_compression_residual_posSemidef Y B
      (1 : Matrix ι ι ℂ) hY hB (by simpa using hBY)
  have ht := (hi.conjTranspose_mul_mul_same E).trace_nonneg
  have hr := (Complex.nonneg_iff.mp ht).1
  rw [hE.eq, Matrix.trace_mul_cycle] at hr
  simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hr

/-- The full spectral Hessian estimate. The comparison `Y ≤ B` strengthens the
inverse term; no commutation assumptions on `X`, `E`, `B`, or `Y` are needed. -/
theorem hessian_nonneg (B Y X E : Matrix ι ι ℂ)
    (hB : B.PosDef) (hY : Y.PosDef) (hBY : (B-Y).PosSemidef)
    (hX : X.IsHermitian) (hE : E.IsHermitian) :
    0 ≤ (Matrix.trace (X * X * B)).re + 2 * (Matrix.trace (X * E)).re +
      (Matrix.trace (E * E * Y⁻¹)).re -
      (Matrix.trace (tangent B X E * BetaLog.logDeriv B
        ⟨tangent B X E, tangent_isHermitian B X E hB.1 hX hE⟩)).re +
      (Matrix.trace (doubleComm X B * BetaPowers.logarithm B)).re / 4 := by
  have hbase := base_hessian_nonneg B X E hB hX hE
  have hmono := trace_inverse_mono B Y E hB hY hBY hE
  linarith

end SchurEntropy.ScalarHessian
