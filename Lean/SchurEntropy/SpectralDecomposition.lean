import SchurEntropy.Definitions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite convex decompositions into rank-one positive matrices

The square-root factorization of a positive matrix gives a sum of outer
products. Rescaling the vectors by the square root of the dimension makes
this a convex combination with strictly positive uniform weights. The
vectors need not be normalized, exactly as in the manuscript.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace SchurEntropy

/-- Every positive matrix on a nonempty finite space is a convex combination
of outer products, with the uniform strictly positive weights `1 / card ι`.
This includes the zero matrix: the corresponding vectors may be zero.
-/
theorem exists_uniform_rankOne_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.PosSemidef) :
    ∃ u : ι → ι → ℂ,
      (∑ a, (1 / (Fintype.card ι : ℝ)) •
        Matrix.vecMulVec (u a) (star (u a))) = H := by
  obtain ⟨B, hB⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self (a := H)).mp hH.nonneg
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos
  have hc : ((1 / d : ℝ) : ℂ) * (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [mul_assoc, Real.mul_self_sqrt hd.le]
    exact one_div_mul_cancel (ne_of_gt hd)
  refine ⟨fun a i => (Real.sqrt d : ℂ) * star (B a i), ?_⟩
  rw [hB]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj,
    Complex.real_smul, Matrix.mul_apply, Matrix.star_apply]
  apply Finset.sum_congr rfl
  intro a ha
  change ((1 / d : ℝ) : ℂ) *
      ((Real.sqrt d : ℂ) * star (B a i) * (B a j * (Real.sqrt d : ℂ))) =
    star (B a i) * B a j
  calc
    _ = (((1 / d : ℝ) : ℂ) * (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ)) *
      (star (B a i) * B a j) := by ring
    _ = _ := by rw [hc, one_mul]

theorem uniform_rankOne_weights_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    0 < 1 / (Fintype.card ι : ℝ) := by
  have h : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  positivity

theorem uniform_rankOne_weights_sum
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    (∑ _a : ι, 1 / (Fintype.card ι : ℝ)) = 1 := by
  have h : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := ι))
  simp [h]

end SchurEntropy
