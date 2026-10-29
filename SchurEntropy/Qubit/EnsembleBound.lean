import SchurEntropy.Qubit.EnsembleEntropy
import SchurEntropy.Qubit.EnsembleScalar
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.Qubit

variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K]

omit [DecidableEq D] in
theorem bform_finite_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (σ : ι → Matrix D D ℂ) (a : D → ℂ) :
    (bform (∑ i, p i • σ i) a a).re = ∑ i, p i * (bform (σ i) a a).re := by
  simp only [bform, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

namespace QubitOutputForm
variable (N : QubitOutputForm D J K)

theorem masses_finite_mix {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (σ : ι → Matrix D D ℂ) :
    N.mx (∑ i, p i • σ i) = ∑ i, p i * N.mx (σ i) ∧
    N.my (∑ i, p i • σ i) = ∑ i, p i * N.my (σ i) ∧
    N.mz (∑ i, p i • σ i) = ∑ i, p i * N.mz (σ i) ∧
    N.mw (∑ i, p i • σ i) = ∑ i, p i * N.mw (σ i) := by
  refine ⟨bform_finite_mix p σ N.a, ?_, bform_finite_mix p σ N.c, ?_⟩
  · simp only [my, bform_finite_mix, Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp only [mw, bform_finite_mix, Finset.mul_sum]
    rw [Finset.sum_comm]

/-- In arbitrary input dimension, a finite input ensemble has the original
average state and average output entropy bounded by the scalar comparison
matrix. The frame balances the two coherent probabilities on every atom. -/
theorem scalar_bound [Nonempty D] (h : N.Complete) (ρ : MState D) :
    ∃ (k : ℕ) (E : MEnsemble D (Fin k)), Ensemble.mix E = ρ ∧
      avgOutputEntropy (N.toCPTP h) E ≤
        OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx ρ.m) (N.my ρ.m)
          (N.mz ρ.m) (N.mw ρ.m)) := by
  obtain ⟨v, hv, hbal⟩ := exists_ratio_frame ρ N.a N.c
  have hmass := sum_vecMass_eq_one ρ v hv
  let E : MEnsemble D (D → Bool) := vecEnsemble v hmass
  have hmix : Ensemble.mix E = ρ := by
    apply MState.ext_m
    exact (vecEnsemble_mix_m v hmass).trans hv
  have hρ : ρ.m = ∑ i, vecMass (v i) • (vecState (v i)).m := by
    rw [← hv]
    exact Finset.sum_congr rfl fun i _ => (vecMass_smul_vecState_m (v i)).symm
  obtain ⟨hx, hy, hz, hw⟩ := N.masses_finite_mix (fun i => vecMass (v i))
    (fun i => (vecState (v i)).m)
  rw [← hρ] at hx hy hz hw
  have hratio (i : D → Bool) (hi : 0 < vecMass (v i)) :
      (∑ j, vecMass (v j) * N.mz (vecState (v j)).m) * N.mx (vecState (v i)).m =
      (∑ j, vecMass (v j) * N.mx (vecState (v j)).m) * N.mz (vecState (v i)).m := by
    rw [← hx, ← hz]
    have hb := hbal i
    rw [← vecMass_smul_vecState_m, bform_smul, bform_smul] at hb
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hb
    change N.mz ρ.m * (vecMass (v i) * N.mx (vecState (v i)).m) =
      N.mx ρ.m * (vecMass (v i) * N.mz (vecState (v i)).m) at hb
    nlinarith
  have hsqrt := sum_weighted_sqrt_mul_eq_of_balance
    (fun i => vecMass (v i)) (fun i => N.mx (vecState (v i)).m)
    (fun i => N.mz (vecState (v i)).m) (fun i => vecMass_nonneg (v i))
    (fun i => (N.masses_nonneg (matrix_isState (vecState (v i))).1).1)
    (fun i => (N.masses_nonneg (matrix_isState (vecState (v i))).1).2.2.1) hratio
  rw [← hx, ← hz] at hsqrt
  let T : (D → Bool) → Matrix (Fin 2) (Fin 2) ℂ := fun i =>
    tc4ScalarMatrix (N.mx (vecState (v i)).m) (N.my (vecState (v i)).m)
      (N.mz (vecState (v i)).m) (N.mw (vecState (v i)).m)
  have hT : (∑ i, vecMass (v i) • T i) =
      tc4ScalarMatrix (N.mx ρ.m) (N.my ρ.m) (N.mz ρ.m) (N.mw ρ.m) := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [T, tc4ScalarMatrix, Matrix.sum_apply,
      Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      ← Complex.ofReal_add]
    · simp only [mul_add, Finset.sum_add_distrib, ← hx, ← hy]
    · exact hsqrt
    · exact hsqrt
    · simp only [mul_add, Finset.sum_add_distrib, ← hz, ← hw]
  have hTpsd (i : D → Bool) : (T i).PosSemidef := by
    obtain ⟨h0,h1,h2,h3⟩ := N.masses_nonneg (matrix_isState (vecState (v i))).1
    exact tc4ScalarMatrix_posSemidef _ _ _ _ h0 h1 h2 h3
  have hj := OpenAIEntropy.concaveOn_entropy.le_map_sum
    (t := Finset.univ) (w := fun i => vecMass (v i)) (p := T)
    (fun i _ => vecMass_nonneg (v i)) hmass (fun i _ => hTpsd i)
  simp only [smul_eq_mul] at hj
  rw [hT] at hj
  have hbound : avgOutputEntropy (N.toCPTP h) E ≤
      OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx ρ.m) (N.my ρ.m)
        (N.mz ρ.m) (N.mw ρ.m)) := by
    change (∑ i, vecMass (v i) * Sᵥₙ (N.toCPTP h (vecState (v i)))) ≤ _
    have he (i : D → Bool) : Sᵥₙ (N.toCPTP h (vecState (v i))) =
        OpenAIEntropy.entropy (N.act (vecState (v i)).m) := by
      rw [entropy_eq_openai, N.toCPTP_m]
    simp_rw [he, N.weighted_entropy_vecState]
    exact hj
  refine ⟨Fintype.card (D → Bool), Ensemble.congrMEnsemble (Fintype.equivFin _) E, ?_, ?_⟩
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    exact hmix
  · rw [avgOutputEntropy_reindex]
    exact hbound

end QubitOutputForm
end SchurEntropy.Qubit
