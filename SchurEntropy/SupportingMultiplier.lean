import SchurEntropy.ScalarConvexityCalculus
import SchurEntropy.StrictLogOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Matrix Filter Set
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace SchurEntropy.SupportingMultiplier
open QubitAdditivity SchurEntropy.ScalarConvexity

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

@[simp] theorem logarithm_scalarDiagonal {m : ℕ} (y : Fin m → ℝ) :
    BetaPowers.logarithm (scalarDiagonal y) = scalarDiagonal (fun i => Real.log (y i)) := by
  exact Matrix.cfc_diagonal y Real.log

/-- The gradient in the noise coordinates, with the base-two conversion explicit. -/
def noiseMultiplier {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => (Real.log (y i) - (BetaPowers.logarithm (A + scalarDiagonal y) i i).re) /
    Real.log 2

theorem scalarDiagonal_posDef {m : ℕ} {y : Fin m → ℝ} (hy : ∀ i, 0 < y i) :
    (scalarDiagonal y).PosDef :=
  Matrix.PosDef.diagonal (fun i => by exact_mod_cast hy i)

/-- The scalar entropy deficit is differentiable in every noise direction at
strictly positive noise weights, even when the signal matrix is singular. -/
theorem hasDerivAt_scalarDeficit_noise {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.PosSemidef)
    (y d : Fin m → ℝ) (hy : ∀ i, 0 < y i) :
    HasDerivAt (fun t : ℝ => scalarDeficit A (scalarDiagonal (y + t • d)))
      (dot (noiseMultiplier A y) d) 0 := by
  let a : HermitianMat (Fin m) ℂ := ⟨A, hA.isHermitian⟩
  let b : ℝ → HermitianMat (Fin m) ℂ :=
    fun t => HermitianMat.diagonal ℂ (y + t • d)
  have hb : HasDerivAt b (HermitianMat.diagonal ℂ d) 0 := by
    exact (diagonalCLM (n := Fin m)).hasFDerivAt.comp_hasDerivAt 0
      (by simpa using (((hasDerivAt_id (0 : ℝ)).smul_const d).const_add y))
  have hbp : (b 0).mat.PosDef := by simpa [b] using hy
  have habp : (a + b 0).mat.PosDef := Matrix.PosDef.posSemidef_add hA hbp
  have h1 := hasDerivAt_entropy_bits_path habp (hb.const_add a)
  have h2 := hasDerivAt_entropy_bits_path hbp hb
  have hd := (h1.sub_const (entropy (Matrix.diagonal A.diag))).sub h2
  convert hd using 1
  · ext t
    rfl
  · simp only [b, zero_smul, add_zero, HermitianMat.mat_add, a, HermitianMat.mat_mk]
    change dot (noiseMultiplier A y) d =
      -(scalarDiagonal d * (BetaPowers.logarithm (A + scalarDiagonal y) + 1)).trace.re /
          Real.log 2 -
        -(scalarDiagonal d * (BetaPowers.logarithm (scalarDiagonal y) + 1)).trace.re /
          Real.log 2
    have htrace (B : Matrix (Fin m) (Fin m) ℂ) :
        (scalarDiagonal d * B).trace.re = ∑ i, d i * (B i i).re := by
      simp [scalarDiagonal, Matrix.trace, Matrix.diagonal_mul, Complex.mul_re]
    rw [logarithm_scalarDiagonal, htrace, htrace]
    simp only [dot, noiseMultiplier, Matrix.add_apply, Matrix.one_apply_eq,
      Complex.add_re, Complex.one_re, scalarDiagonal, Matrix.diagonal_apply_eq,
      Complex.ofReal_re]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← sub_div, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Every coordinate of the noise gradient is strictly negative whenever
the corresponding signal diagonal is positive. -/
theorem noiseMultiplier_neg {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.PosSemidef)
    (y : Fin m → ℝ) (hy : ∀ i, 0 < y i)
    (hdiag : ∀ i, 0 < (A i i).re) (i : Fin m) :
    noiseMultiplier A y i < 0 := by
  have hlt := StrictLogOrder.logarithm_diagonal_lt
    (W := ⟨scalarDiagonal y, scalarDiagonal_conjTranspose y⟩)
    (H := ⟨A, hA.isHermitian⟩) (scalarDiagonal_posDef hy) hA (hdiag i)
  change (BetaPowers.logarithm (scalarDiagonal y) i i).re <
    (BetaPowers.logarithm (scalarDiagonal y + A) i i).re at hlt
  rw [logarithm_scalarDiagonal, add_comm (scalarDiagonal y) A] at hlt
  have hlt' : Real.log (y i) < (BetaPowers.logarithm (A + scalarDiagonal y) i i).re := by
    simpa [scalarDiagonal] using hlt
  exact div_neg_of_neg_of_pos (sub_neg.mpr hlt') (Real.log_pos (by norm_num))

/-- Joint convexity gives the global supporting inequality in the noise
variable at every strictly positive noise vector. -/
theorem noise_support (hScalar : ScalarConvexityStatement)
    {m : ℕ} (hm : 0 < m) (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.PosSemidef)
    (r y : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (hy : ∀ i, 0 < y i)
    (z : Fin m → ℝ) (hz : ∀ i, 0 ≤ z i) :
    scalarFunction C r y + dot (noiseMultiplier (scalarSkeleton C r) y) (z - y) ≤
      scalarFunction C r z := by
  let p : ℝ →ᵃ[ℝ] ((Fin m → ℝ) × (Fin m → ℝ)) :=
    AffineMap.lineMap (r, y) (r, z)
  have hc := (hScalar m C hm hC).comp_affineMap p
  have hd : HasDerivAt ((fun q => scalarFunction C q.1 q.2) ∘ p)
      (dot (noiseMultiplier (scalarSkeleton C r) y) (z - y)) 0 := by
    have hd' := hasDerivAt_scalarDeficit_noise (scalarSkeleton C r)
      (scalarSkeleton_posSemidef hC r) y (z - y) hy
    simpa [p, Function.comp_def, AffineMap.lineMap_apply_module',
      Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, scalarFunction, add_comm] using hd'
  have h0 : (0 : ℝ) ∈ p ⁻¹' {q : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ q.1 i) ∧ (∀ i, 0 ≤ q.2 i)} := by
    simpa [p] using And.intro hr (fun i => (hy i).le)
  have h1 : (1 : ℝ) ∈ p ⁻¹' {q : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ q.1 i) ∧ (∀ i, 0 ≤ q.2 i)} := by
    simpa [p] using And.intro hr hz
  have hi := hc.le_slope_of_hasDerivAt h0 h1 zero_lt_one hd
  have hi' : dot (noiseMultiplier (scalarSkeleton C r) y) (z - y) ≤
      scalarFunction C r z - scalarFunction C r y := by
    simpa [p, slope_def_field] using hi
  linarith

/-- A positive coefficient matrix and strictly positive signal/noise weights
supply exactly the negative multiplier needed by the block reduction. -/
theorem exists_negative_support (hScalar : ScalarConvexityStatement)
    {m : ℕ} (hm : 0 < m) (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.PosDef)
    (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (y : Fin m → ℝ) (hy : ∀ i, 0 < y i) :
    ∃ μ : Fin m → ℝ, (∀ i, μ i < 0) ∧
      ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
        scalarFunction C r y + dot μ (z - y) ≤ scalarFunction C r z := by
  refine ⟨noiseMultiplier (scalarSkeleton C r) y, ?_, ?_⟩
  · apply noiseMultiplier_neg _ (scalarSkeleton_posSemidef hC.posSemidef r) y hy
    intro i
    have hcii : 0 < (C i i).re := (Complex.pos_iff.mp hC.diag_pos).1
    have hs := Real.sqrt_pos.mpr (hr i)
    simpa [scalarSkeleton, scalarDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Complex.mul_re] using mul_pos (mul_pos hs hcii) hs
  · exact noise_support hScalar hm C hC.posSemidef r y (fun i => (hr i).le) hy

end SchurEntropy.SupportingMultiplier
