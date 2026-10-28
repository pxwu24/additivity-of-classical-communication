import SchurEntropy.ScalarConvexityAlgebra
import SchurEntropy.ScalarConvexityBridge
import SchurEntropy.ScalarConvexityBoundary

/-!
# Joint convexity of the scalar block entropy deficit

The proof differentiates the spectral entropy on strictly positive weights,
uses the logarithmic-mean Hessian estimate, and extends to zero weights by
continuity. The coefficient matrix may be singular throughout the argument.
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
attribute [local instance] mNorm mSpace mTop mAdd mModule hTop hAdd hModule

/-- Every affine path that stays in positive weights has convex entropy deficit. -/
theorem convexOn_deficitPath (C : HermitianMat n ℂ) (hC : C.mat.PosSemidef)
    (r y h k : n → ℝ)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, 0 < r i + t * h i)
    (hy : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, 0 < y i + t * k i) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (deficitPath C (fun i => (C.mat i i).re) r y h k) := by
  have hc : ∀ i, 0 ≤ (C.mat i i).re :=
    fun i => (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    hasDerivAt_deficitPath C (fun i => (C.mat i i).re) r y h k t hc
      (hr t ht) (hy t ht) (outputPath_posDef C hC r y h k t (hy t ht))
  have hd₂ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    hasDerivAt_deficitPath₁ C (fun i => (C.mat i i).re) r y h k t hc
      (hr t ht) (hy t ht) (outputPath_posDef C hC r y h k t (hy t ht))
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => (hd₂ t (interior_subset ht)).hasDerivWithinAt) ?_
  intro t ht
  exact deficitPath₂_nonneg C hC r y h k t
    (hr t (interior_subset ht)) (hy t (interior_subset ht))

lemma positive_weighted_sum {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : 0 < x) (hy : 0 < y) : 0 < a * x + b * y := by
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    simpa [hb1] using hy
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx)
      (mul_nonneg hb hy.le)

lemma positive_affine_segment {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < x + t * (y - x) := by
  have hh := positive_weighted_sum (sub_nonneg.mpr ht.2) ht.1
    (show (1 - t) + t = 1 by ring) hx hy
  nlinarith

/-- Joint convexity on strictly positive scalar weights. -/
theorem scalarFunction_convexOn_positive {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : C.PosSemidef) :
    ConvexOn ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i)}
      (fun p => scalarFunction C p.1 p.2) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    constructor
    · intro i
      exact positive_weighted_sum ha hb hab (hx.1 i) (hy.1 i)
    · intro i
      exact positive_weighted_sum ha hb hab (hx.2 i) (hy.2 i)
  · intro x hx y hy a b ha hb hab
    let CH : HermitianMat (Fin m) ℂ := ⟨C, hC.isHermitian⟩
    let h : Fin m → ℝ := fun i => y.1 i - x.1 i
    let k : Fin m → ℝ := fun i => y.2 i - x.2 i
    have hr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin m) :
        0 < x.1 i + t * h i := positive_affine_segment (hx.1 i) (hy.1 i) ht
    have hw (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin m) :
        0 < x.2 i + t * k i := positive_affine_segment (hx.2 i) (hy.2 i) ht
    have hconv := convexOn_deficitPath CH hC x.1 x.2 h k hr hw
    have hj := hconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ha hb hab
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hj
    have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨hb, by linarith⟩
    have he0 := scalarFunction_eq_deficitPath CH x.1 x.2 h k 0
      (fun i => (hr 0 (by norm_num) i).le)
    have he1 := scalarFunction_eq_deficitPath CH x.1 x.2 h k 1
      (fun i => (hr 1 (by norm_num) i).le)
    have heb := scalarFunction_eq_deficitPath CH x.1 x.2 h k b
      (fun i => (hr b hbI i).le)
    have hm₁ : (fun i => x.1 i + b * h i) = (a • x + b • y).1 := by
      funext i
      change x.1 i + b * (y.1 i - x.1 i) = a * x.1 i + b * y.1 i
      rw [show a = 1 - b by linarith]
      ring
    have hm₂ : (fun i => x.2 i + b * k i) = (a • x + b • y).2 := by
      funext i
      change x.2 i + b * (y.2 i - x.2 i) = a * x.2 i + b * y.2 i
      rw [show a = 1 - b by linarith]
      ring
    simp only [zero_mul, add_zero] at he0
    simp only [h, k, one_mul, add_sub_cancel] at he1
    rw [hm₁, hm₂] at heb
    change scalarFunction C (a • x + b • y).1 (a • x + b • y).2 ≤
      a * scalarFunction C x.1 x.2 + b * scalarFunction C y.1 y.2
    change scalarFunction C x.1 x.2 = _ at he0
    change scalarFunction C y.1 y.2 = _ at he1
    change scalarFunction C (a • x + b • y).1 (a • x + b • y).2 = _ at heb
    rw [he0, he1, heb]
    have hlog : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    convert div_le_div_of_nonneg_right hj hlog using 1
    ring

end SchurEntropy.ScalarConvexity

namespace SchurEntropy

/-- The scalar joint convexity lemma, including singular `C` and zero weights. -/
theorem scalar_joint_convexity : ScalarConvexityStatement :=
  scalarConvexity_of_positive (fun _ C _ hC => ScalarConvexity.scalarFunction_convexOn_positive C hC)

end SchurEntropy
