import QubitAdditivity.NormalForm
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# Output-basis selection in arbitrary finite input dimension

The off-diagonal dual block after a qubit output rotation is a homogeneous
quadratic matrix pencil. Its determinant is a homogeneous complex polynomial
of positive degree, so it has a nonzero projective zero. Unlike an arbitrary
polynomial in variables and their conjugates, this polynomial is holomorphic.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Polynomial
open scoped Matrix BigOperators ComplexOrder

namespace SchurEntropy.Qubit
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant polynomial of a quadratic matrix pencil. -/
def quadraticDet (A B C : Matrix n n ℂ) : ℂ[X] :=
  Matrix.det (Matrix.of fun i j => Polynomial.C (A i j) * X ^ 2 +
    Polynomial.C (B i j) * X + Polynomial.C (C i j))

/-- The highest possible coefficient is the determinant of the leading matrix. -/
theorem quadraticDet_top (A B C : Matrix n n ℂ) :
    (quadraticDet A B C).coeff (Fintype.card n * 2) = A.det := by
  rw [quadraticDet, Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro g _
  convert! Polynomial.coeff_smul (R := ℂ) (Equiv.Perm.sign g) _ _
  convert! (Polynomial.coeff_prod_of_natDegree_le (R := ℂ) _ _ 2 _).symm
  · simp
  · intro p _
    apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · exact Polynomial.natDegree_C_mul_X_pow_le _ 2
      · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp

theorem quadraticDet_eval (A B C : Matrix n n ℂ) (z : ℂ) :
    (quadraticDet A B C).eval z = (z ^ 2 • A + z • B + C).det := by
  change Polynomial.evalRingHom z _ = _
  rw [quadraticDet, RingHom.map_det]
  congr 1
  ext i j
  simp
  ring

/-- A homogeneous quadratic matrix pencil of positive size has a singular
value at some normalized complex pair. -/
theorem exists_unit_singular_quadratic [Nonempty n] (A B C : Matrix n n ℂ) :
    ∃ s t : ℂ, Complex.normSq s + Complex.normSq t = 1 ∧
      (s ^ 2 • A + (s * t) • B + t ^ 2 • C).det = 0 := by
  by_cases hdeg : (quadraticDet A B C).degree = 0
  · refine ⟨1, 0, by simp, ?_⟩
    have hn : 0 < Fintype.card n * 2 := Nat.mul_pos Fintype.card_pos (by omega)
    have hc : (quadraticDet A B C).coeff (Fintype.card n * 2) = 0 :=
      Polynomial.coeff_eq_zero_of_degree_lt (by rw [hdeg]; exact_mod_cast hn)
    rw [quadraticDet_top] at hc
    simpa using hc
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (quadraticDet A B C) hdeg
    rw [Polynomial.IsRoot, quadraticDet_eval] at hz
    set r := Complex.normSq z + 1
    have hrpos : 0 < r := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos
    set l : ℝ := 1 / Real.sqrt r
    have hl2 : l ^ 2 * r = 1 := by
      simp only [l, div_pow, one_pow, Real.sq_sqrt hrpos.le]
      field_simp
    refine ⟨(l : ℂ) * z, (l : ℂ), ?_, ?_⟩
    · simp only [Complex.normSq_mul, Complex.normSq_ofReal]
      nlinarith [hl2]
    · have hm : ((l : ℂ) * z) ^ 2 • A + ((l : ℂ) * z * (l : ℂ)) • B +
          (l : ℂ) ^ 2 • C = ((l : ℂ) ^ 2) • (z ^ 2 • A + z • B + C) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hm, Matrix.det_smul, hz, mul_zero]

/-- The matrix pencil occurring in qubit output-basis selection can always
be made singular, in every positive input dimension. -/
theorem exists_unit_singular_cross [Nonempty n] (P R B : Matrix n n ℂ) :
    ∃ s t : ℂ, Complex.normSq s + Complex.normSq t = 1 ∧
      (s ^ 2 • B + (s * t) • (R - P) - t ^ 2 • Bᴴ).det = 0 := by
  obtain ⟨s, t, hst, hdet⟩ := exists_unit_singular_quadratic B (R - P) (-Bᴴ)
  exact ⟨s, t, hst, by simpa only [smul_neg, sub_eq_add_neg] using hdet⟩

end SchurEntropy.Qubit
