import SchurEntropy.Qubit.EnsembleFrame
import SchurEntropy.Qubit.OutputForm

noncomputable section
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.Qubit
variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
theorem bform_outer (v a c : d → ℂ) :
    bform (Matrix.vecMulVec v (star v)) a c =
      (star a ⬝ᵥ v) * (star v ⬝ᵥ c) := by
  simp only [bform, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bform_outer_cross (v a c : d → ℂ) :
    bform (Matrix.vecMulVec v (star v)) a c *
      bform (Matrix.vecMulVec v (star v)) c a =
    bform (Matrix.vecMulVec v (star v)) a a *
      bform (Matrix.vecMulVec v (star v)) c c := by
  simp only [bform_outer]
  ring

theorem bform_vecState_cross [Nonempty d] (v a c : d → ℂ) (hv : vecMass v ≠ 0) :
    bform (vecState v).m a c * bform (vecState v).m c a =
      bform (vecState v).m a a * bform (vecState v).m c c := by
  have hstate : (vecState v).m = (vecMass v)⁻¹ • Matrix.vecMulVec v (star v) := by
    rw [← vecMass_smul_vecState_m, smul_smul, inv_mul_cancel₀ hv, one_smul]
  rw [hstate]
  simp only [bform_smul]
  have h := bform_outer_cross v a c
  linear_combination (((vecMass v)⁻¹ : ℝ) : ℂ)^2 * h

namespace QubitOutputForm
variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K]
variable (N : QubitOutputForm D J K)

theorem entropy_act_of_cross {σ : Matrix D D ℂ} (hσ : σ.PosSemidef)
    (hcross : bform σ N.a N.c * bform σ N.c N.a =
      bform σ N.a N.a * bform σ N.c N.c) :
    OpenAIEntropy.entropy (N.act σ) =
      OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx σ) (N.my σ) (N.mz σ) (N.mw σ)) := by
  have ha : bform σ N.a N.a = (N.mx σ : ℂ) := bform_self_eq_re hσ.1 N.a
  have hc : bform σ N.c N.c = (N.mz σ : ℂ) := bform_self_eq_re hσ.1 N.c
  have hb : ∑ j, bform σ (N.b j) (N.b j) = (N.my σ : ℂ) :=
    sum_bform_self_eq_re hσ.1 N.b
  have hd : ∑ k, bform σ (N.d k) (N.d k) = (N.mw σ : ℂ) :=
    sum_bform_self_eq_re hσ.1 N.d
  obtain ⟨hx, -, hz, -⟩ := N.masses_nonneg hσ
  apply entropy_eq_of_trace_det (N.act_isHermitian hσ.1)
    (tc4ScalarMatrix_isHermitian _ _ _ _)
  · rw [N.act_trace hσ.1]
    simp [tc4ScalarMatrix, Matrix.trace_fin_two]
    ring
  · simp only [act, tc4ScalarMatrix, Matrix.det_fin_two_of]
    rw [hcross, ha, hc, hb, hd,
      ← Complex.ofReal_mul (Real.sqrt _), Real.mul_self_sqrt (mul_nonneg hx hz)]
    push_cast
    ring

theorem weighted_entropy_vecState [Nonempty D] (v : D → ℂ) :
    vecMass v * OpenAIEntropy.entropy (N.act (vecState v).m) =
      vecMass v * OpenAIEntropy.entropy
        (tc4ScalarMatrix (N.mx (vecState v).m) (N.my (vecState v).m)
          (N.mz (vecState v).m) (N.mw (vecState v).m)) := by
  by_cases hv : vecMass v = 0
  · simp [hv]
  · rw [N.entropy_act_of_cross (matrix_isState (vecState v)).1
      (bform_vecState_cross v N.a N.c hv)]

end QubitOutputForm
end SchurEntropy.Qubit
