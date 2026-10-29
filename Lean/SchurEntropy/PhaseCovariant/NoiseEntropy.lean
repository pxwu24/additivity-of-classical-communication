/-
The normalization/Jensen argument generalizes the weighted branch entropy
proof in KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/Partner.lean (Apache-2.0).
See third_party/NOTICE and third_party/Apache-2.0.txt.
-/
import QubitAdditivity.Partner
import QubitAdditivity.Imported.EntropyScaling

/-! Entropy concavity for unnormalized mixtures, including zero total mass. -/

noncomputable section
open Matrix QubitAdditivity
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy.PhaseCovariant

variable {I e : Type*} [Fintype I] [Fintype e] [DecidableEq e]

theorem entropy_smul_state_sub (w : ℝ) (σ : MState e) :
    OpenAIEntropy.entropy (w • σ.m) - Real.negMulLog w =
      w * OpenAIEntropy.entropy σ.m := by
  rw [OpenAIEntropy.entropy_smul w σ.psd.isHermitian, σ.tr']
  simp

/-- Jensen's inequality with arbitrary nonnegative masses. The subtraction is
the scalar entropy of their total mass, rather than a normalization assumption. -/
theorem entropy_mixture_sub_ge (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (σ : I → MState e) :
    (∑ i, w i * OpenAIEntropy.entropy (σ i).m) ≤
      OpenAIEntropy.entropy (∑ i, w i • (σ i).m) - Real.negMulLog (∑ i, w i) := by
  classical
  let M := ∑ i, w i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hw i
  rcases hM.lt_or_eq with hpos | hzero
  · let q : I → ℝ := fun i => w i / M
    have hq : ∀ i, 0 ≤ q i := fun i => div_nonneg (hw i) hpos.le
    have hqsum : ∑ i, q i = 1 := by
      change (∑ i, w i / M) = 1
      rw [← Finset.sum_div]
      exact div_self hpos.ne'
    let T : Matrix e e ℂ := ∑ i, q i • (σ i).m
    have hT : T.PosSemidef :=
      Matrix.posSemidef_sum _ fun i _ => (σ i).psd.smul (hq i)
    have hTtr : T.trace.re = 1 := by
      simp only [T, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
        MState.tr', Complex.real_smul, Complex.ofReal_re, mul_one]
      exact hqsum
    have hscale : (∑ i, w i • (σ i).m) = M • T := by
      simp only [T, Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      dsimp [q]
      field_simp
    have hj := OpenAIEntropy.concaveOn_entropy.le_map_sum (t := Finset.univ)
      (w := q) (p := fun i => (σ i).m) (fun i _ => hq i) hqsum
      (fun i _ => (σ i).psd)
    have hsum : (∑ i, w i * OpenAIEntropy.entropy (σ i).m) =
        M * ∑ i, q i * OpenAIEntropy.entropy (σ i).m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [q]
      field_simp
    rw [hscale, OpenAIEntropy.entropy_smul M hT.isHermitian, hTtr, mul_one,
      add_sub_cancel_right, hsum]
    exact mul_le_mul_of_nonneg_left hj hpos.le
  · have hwzero (i : I) : w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw j).mp hzero.symm i
        (Finset.mem_univ i)
    simp [hwzero, OpenAIEntropy.entropy]

end SchurEntropy.PhaseCovariant
