import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Finite weighted logarithms at a semidefinite boundary

A lower bound on a regularized logarithmic pairing forces all weights on
zero spectral values to vanish. The regularized pairing then converges to
the spectral logarithm extended by zero at zero.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace SchurEntropy.Capacity

variable {ι : Type*} [Fintype ι]

theorem weight_zero_of_log_shift_bddBelow
    (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, 0 ≤ v i)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, B ≤ ∑ i, a i * Real.log (v i + t))
    (i : ι) (hi : v i = 0) : a i = 0 := by
  classical
  by_contra hne
  have hp : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
  let C : ℝ := ∑ j ∈ Finset.univ.erase i, a j * Real.log (v j + 1)
  have hupper (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
      (∑ j, a j * Real.log (v j + t)) ≤ a i * Real.log t + C := by
    have hsum : (∑ j ∈ Finset.univ.erase i, a j * Real.log (v j + t)) ≤ C := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (ha j)
      exact Real.log_le_log (add_pos_of_nonneg_of_pos (hv j) ht)
        (by linarith)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hi, zero_add]
    linarith
  have hl : Tendsto (fun t : ℝ => a i * Real.log t) (𝓝[>] 0) atBot :=
    (tendsto_const_mul_atBot_of_pos hp).mpr Real.tendsto_log_nhdsGT_zero
  have hc : Tendsto (fun t : ℝ => a i * Real.log t + C) (𝓝[>] 0) atBot :=
    tendsto_atBot_add_const_right _ _ hl
  obtain ⟨B, hB⟩ := hb
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have htone : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, hbt, hct, htp, ht₁⟩ :=
    (hB.and ((hc.eventually_lt_atBot B).and (htpos.and htone))).exists
  exact (not_lt_of_ge (hbt.trans (hupper t htp ht₁))) hct

theorem tendsto_sum_log_shift_of_bddBelow
    (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, 0 ≤ v i)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, B ≤ ∑ i, a i * Real.log (v i + t)) :
    Tendsto (fun t : ℝ => ∑ i, a i * Real.log (v i + t)) (𝓝[>] 0)
      (𝓝 (∑ i, a i * Real.log (v i))) := by
  apply tendsto_finsetSum
  intro i _
  by_cases hi : v i = 0
  · have hz := weight_zero_of_log_shift_bddBelow a v ha hv hb i hi
    simp only [hz, zero_mul]
    exact tendsto_const_nhds
  · have hc : ContinuousAt (fun t : ℝ => a i * Real.log (v i + t)) 0 :=
      continuousAt_const.mul ((Real.continuousAt_log (by simpa using hi)).comp
        (continuousAt_const.add continuousAt_id))
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

end SchurEntropy.Capacity
