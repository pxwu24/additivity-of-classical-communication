import QubitAdditivity.BetaGramSplit
import QubitAdditivity.PureInput
import SchurEntropy.Definitions

/-!
# Finite pure decompositions with one balanced expectation

The redundant spectral sign frame is the finite flat-frame alternative to the
Fourier basis in the manuscript. Zero vectors are retained with zero probability.
-/

noncomputable section
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace SchurEntropy.Qubit

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
theorem bform_trace_outer (A : Matrix d d ℂ) (a b : d → ℂ) :
    bform A a b = (A * Matrix.vecMulVec b (star a)).trace := by
  simp only [bform, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.star_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An exact rank-one decomposition of a state with zero expectation of a
specified Hermitian constraint on every unnormalized vector. -/
theorem exists_balanced_frame (ρ : MState d) (K : HermitianMat d ℂ)
    (hK : (K.mat * ρ.m).trace = 0) :
    ∃ v : (d → Bool) → d → ℂ,
      (∑ f, Matrix.vecMulVec (v f) (star (v f))) = ρ.m ∧
      ∀ f, bform K.mat (v f) (v f) = 0 := by
  obtain ⟨B, hB⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := ρ.m)).mp
    (matrix_isState ρ).1.nonneg
  let X : Matrix d d ℂ := Bᴴ
  have hX : X * Xᴴ = ρ.m := by
    dsimp [X]
    rw [Matrix.conjTranspose_conjTranspose]
    exact hB.symm
  let H : HermitianMat d ℂ := ⟨Xᴴ * K.mat * X, Matrix.isHermitian_conjTranspose_mul_mul X K.H⟩
  have hH : H.mat.trace = 0 := by
    change (Xᴴ * K.mat * X).trace = 0
    rw [Matrix.trace_mul_cycle, hX]
    rw [Matrix.trace_mul_comm]
    exact hK
  let c : ℝ := (Fintype.card (d → Bool) : ℝ)⁻¹
  have hc0 : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcard : (Fintype.card (d → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  let v : (d → Bool) → d → ℂ := fun f => Real.sqrt c •
    (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f)
  refine ⟨v, ?_, ?_⟩
  · have hs := QubitAdditivity.BetaGramSplit.sum_image_outer X H
    have hv : (∑ f, Matrix.vecMulVec (v f) (star (v f))) =
        c • (∑ f, QubitAdditivity.BetaGramSplit.outer
          (fun i => (X * QubitAdditivity.BetaSignFrame.spectralFrame H) i f)).mat := by
      rw [QubitAdditivity.BetaGramSplit.mat_sum]
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro f _
      change (QubitAdditivity.BetaGramSplit.outer (v f)).mat =
        c • (QubitAdditivity.BetaGramSplit.outer
          (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f)).mat
      rw [show v f = Real.sqrt c • (X *ᵥ fun i =>
        QubitAdditivity.BetaSignFrame.spectralFrame H i f) from rfl,
        QubitAdditivity.BetaGramSplit.outer_sqrt_smul hc0]
      rfl
    rw [hv, hs, hX]
    have he : (Fintype.card (d → Bool) : ℂ) • ρ.m =
        (Fintype.card (d → Bool) : ℝ) • ρ.m := by
      ext i j
      simp [Complex.real_smul]
    rw [he, smul_smul]
    simp [c]
  · intro f
    have hq := QubitAdditivity.BetaSignFrame.spectralFrame_quadratic_zero hH f
    have hq' : bform K.mat (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f)
        (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f) = 0 := by
      change QubitAdditivity.BetaComparison.pairing
        (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f) K.mat
        (X *ᵥ fun i => QubitAdditivity.BetaSignFrame.spectralFrame H i f) = 0
      rw [QubitAdditivity.BetaComparison.pairing_mulVec_left,
        QubitAdditivity.BetaComparison.pairing_mulVec_right]
      exact hq
    dsimp [v]
    simp only [bform, star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, smul_smul]
    change (Real.sqrt c * Real.sqrt c) • bform K.mat _ _ = 0
    rw [hq', smul_zero]

/-- The masses of an exact rank-one state decomposition form a probability distribution. -/
theorem sum_vecMass_eq_one {ι : Type*} [Fintype ι]
    (ρ : MState d) (v : ι → d → ℂ)
    (hv : (∑ f, Matrix.vecMulVec (v f) (star (v f))) = ρ.m) :
    ∑ f, vecMass (v f) = 1 := by
  have h := congrArg (fun A : Matrix d d ℂ => A.trace.re) hv
  simpa only [Matrix.trace_sum, Complex.re_sum, trace_vecMulVec_re, MState.tr',
    Complex.one_re] using h

theorem bform_outer_swap (v a : d → ℂ) :
    bform (Matrix.vecMulVec v (star v)) a a =
      bform (Matrix.vecMulVec a (star a)) v v := by
  rw [bform_trace_outer, bform_trace_outer, Matrix.trace_mul_comm]

/-- The frame specializes to the ratio of two nonnegative quadratic expectations. -/
theorem exists_ratio_frame (ρ : MState d) (a c : d → ℂ) :
    ∃ v : (d → Bool) → d → ℂ,
      (∑ f, Matrix.vecMulVec (v f) (star (v f))) = ρ.m ∧
      ∀ f, (bform ρ.m c c).re *
          (bform (Matrix.vecMulVec (v f) (star (v f))) a a).re =
        (bform ρ.m a a).re *
          (bform (Matrix.vecMulVec (v f) (star (v f))) c c).re := by
  let A : HermitianMat d ℂ := QubitAdditivity.BetaGramSplit.outer a
  let C : HermitianMat d ℂ := QubitAdditivity.BetaGramSplit.outer c
  let x : ℝ := (bform ρ.m a a).re
  let z : ℝ := (bform ρ.m c c).re
  let K : HermitianMat d ℂ := z • A - x • C
  have hK : (K.mat * ρ.m).trace = 0 := by
    change ((z • A.mat - x • C.mat) * ρ.m).trace = 0
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm A.mat, Matrix.trace_mul_comm C.mat]
    change z • (ρ.m * Matrix.vecMulVec a (star a)).trace -
      x • (ρ.m * Matrix.vecMulVec c (star c)).trace = 0
    rw [← bform_trace_outer, ← bform_trace_outer,
      bform_self_eq_re (matrix_isState ρ).1.1 a,
      bform_self_eq_re (matrix_isState ρ).1.1 c]
    simp only [Complex.real_smul]
    dsimp [x,z]
    ring
  obtain ⟨v, hv, hb⟩ := exists_balanced_frame ρ K hK
  refine ⟨v, hv, ?_⟩
  intro f
  have h := congrArg Complex.re (hb f)
  have he : bform K.mat (v f) (v f) =
      z * bform A.mat (v f) (v f) - x * bform C.mat (v f) (v f) := by
    simp only [K, HermitianMat.mat_sub, HermitianMat.mat_smul, bform,
      Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      Complex.real_smul]
  rw [he] at h
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at h
  rw [bform_outer_swap (v f) a, bform_outer_swap (v f) c]
  exact sub_eq_zero.mp h

end SchurEntropy.Qubit
