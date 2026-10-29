import SchurEntropy.Qubit.RankFactorization

/-! Zero padding preserves all Gram sums in a finite Kraus family. -/

noncomputable section
open scoped Matrix BigOperators ComplexConjugate

namespace SchurEntropy.Qubit

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A singular square complex matrix has at most one less than full rank. -/
theorem rank_le_card_sub_one_of_det_eq_zero (B : Matrix n n ℂ) (hB : B.det = 0) :
    B.rank ≤ Fintype.card n - 1 := by
  have hle := B.rank_le_card_width
  have hne : B.rank ≠ Fintype.card n := by
    intro heq
    have htop : LinearMap.range B.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using heq
    have hsurj : Function.Surjective B.mulVec := LinearMap.range_eq_top.mp htop
    have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    exact (Matrix.isUnit_iff_isUnit_det B).mp hu |>.ne_zero hB
  omega

/-- Append zero vectors to a finite family. -/
def padFamily {r s : ℕ} (_h : r ≤ s) (a : Fin r → n → ℂ) : Fin s → n → ℂ :=
  fun j => if hj : j.val < r then a ⟨j.val, hj⟩ else 0

/-- Appending zeros preserves the mixed Gram sum, including its two diagonal
specializations. -/
theorem sum_outer_padFamily {r s : ℕ} (h : r ≤ s)
    (a : Fin r → n → ℂ) (b : Fin r → m → ℂ) :
    (∑ j, Matrix.vecMulVec (padFamily h a j) (star (padFamily h b j))) =
      ∑ j, Matrix.vecMulVec (a j) (star (b j)) := by
  classical
  symm
  apply Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro j hj
    have hnot : ¬j.val < r := by
      intro hjr
      apply hj
      exact ⟨⟨j.val, hjr⟩, Fin.ext rfl⟩
    simp [padFamily, hnot]
  · intro j
    simp [padFamily, j.isLt]

end SchurEntropy.Qubit
