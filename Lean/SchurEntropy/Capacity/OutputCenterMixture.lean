import QubitAdditivity.UpperBound
import QubitAdditivity.BetaEntropy
import QubitAdditivity.Imported.EntropyScaling

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy.Capacity
open QubitAdditivity QubitAdditivity.BetaEntropy

variable {d e α : Type*} [Fintype d] [DecidableEq d]
  [Fintype e] [DecidableEq e] [Fintype α]

/-- Add one signal state to a finite ensemble with normalized outer weights. -/
def appendSingleton (E : MEnsemble d α) (ρ : MState d) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : MEnsemble d (α ⊕ Unit) :=
  ⟨Sum.elim E.states (fun _ => ρ),
    ProbDistribution.mk' (Sum.elim (fun i => a * (E.distr i : ℝ)) (fun _ => b))
      (fun i => by cases i with
        | inl i => exact mul_nonneg ha Prob.zero_le_coe
        | inr _ => exact hb)
      (by simp [Fintype.sum_sum_type, ← Finset.mul_sum, hab])⟩

theorem appendSingleton_mix (E : MEnsemble d α) (ρ : MState d) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (Ensemble.mix (appendSingleton E ρ a b ha hb hab)).m =
      a • (Ensemble.mix E).m + b • ρ.m := by
  rw [Ensemble.mix_of, Ensemble.mix_of]
  simp only [appendSingleton, MEnsemble.states, Fintype.sum_sum_type, Fintype.sum_unique]
  change (∑ i, (a * (E.distr i : ℝ)) • (E.states i).m) + b • ρ.m = _
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem appendSingleton_output_mix (Φ : CPTPMap d e) (E : MEnsemble d α)
    (ρ : MState d) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (Φ (Ensemble.mix (appendSingleton E ρ a b ha hb hab))).m =
      a • (Φ (Ensemble.mix E)).m + b • (Φ ρ).m := by
  simp only [CPTPMap.mat_coe_eq_apply_mat, appendSingleton_mix, map_add,
    Φ.map.map_smul_of_tower]

theorem appendSingleton_avgOutputEntropy (Φ : CPTPMap d e) (E : MEnsemble d α)
    (ρ : MState d) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    avgOutputEntropy Φ (appendSingleton E ρ a b ha hb hab) =
      a * avgOutputEntropy Φ E + b * Sᵥₙ (Φ ρ) := by
  unfold avgOutputEntropy
  simp only [appendSingleton, MEnsemble.states, Fintype.sum_sum_type, Fintype.sum_unique]
  change (∑ i, (a * (E.distr i : ℝ)) * Sᵥₙ (Φ (E.states i))) + b * Sᵥₙ (Φ ρ) = _
  rw [Finset.mul_sum]
  simp only [mul_assoc]

theorem holevoValue_le_holevo_fintype (Φ : CPTPMap d e) (E : MEnsemble d α) :
    holevoValue Φ E ≤ holevo Φ := by
  rw [← holevoValue_reindex Φ E (Fintype.equivFin α)]
  exact holevoValue_le_holevo Φ _

/-- Optimality bounds every positive mixture with an additional channel output.
No support or nonsingularity assumption is used. -/
theorem optimal_center_entropy_increment_lower (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d)
    {t : ℝ} (ht : 0 < t) :
    -t * (holevo Φ + Sᵥₙ (Φ ρ)) + (1 + t) * Real.log (1 + t) ≤
      psi ((Φ (Ensemble.mix E)).M + t • (Φ ρ).M) - psi (Φ (Ensemble.mix E)).M := by
  let σ := Φ (Ensemble.mix E)
  let τ := Φ ρ
  let a := (1 + t)⁻¹
  have hp : 0 < 1 + t := by linarith
  have ha : 0 ≤ a := (inv_pos.mpr hp).le
  have hb : 0 ≤ t * a := mul_nonneg ht.le ha
  have hab : a + t * a = 1 := by
    dsimp [a]
    field_simp
  let F := appendSingleton E ρ a (t * a) ha hb hab
  have hbound := holevoValue_le_holevo_fintype Φ F
  have havg : avgOutputEntropy Φ F = a * avgOutputEntropy Φ E +
      t * a * Sᵥₙ τ := appendSingleton_avgOutputEntropy Φ E ρ a (t * a) ha hb hab
  have hmix : (Φ (Ensemble.mix F)).m = a • (σ.m + t • τ.m) := by
    rw [appendSingleton_output_mix]
    simp [σ, τ, smul_add, smul_smul, mul_comm]
  have htr : (σ.m + t • τ.m).trace.re = 1 + t := by
    simp [Matrix.trace_add, Matrix.trace_smul]
  have hentropy : Sᵥₙ (Φ (Ensemble.mix F)) =
      a * OpenAIEntropy.entropy (σ.m + t • τ.m) + Real.log (1 + t) := by
    have hHerm : (σ.m + t • τ.m).IsHermitian :=
      σ.Hermitian.add (τ.Hermitian.smul_real t)
    rw [entropy_eq_openai, hmix, OpenAIEntropy.entropy_smul a hHerm, htr]
    dsimp [a]
    rw [Real.negMulLog, Real.log_inv]
    field_simp
  rw [holevoValue_eq, havg, hentropy] at hbound
  rw [holevoValue_eq] at hE
  have hscaled := (mul_le_mul_of_nonneg_left hbound hp.le)
  dsimp [a] at hscaled
  have hscaled' : OpenAIEntropy.entropy (σ.m + t • τ.m) +
      (1 + t) * Real.log (1 + t) - avgOutputEntropy Φ E - t * Sᵥₙ τ ≤
      (1 + t) * holevo Φ := by
    convert hscaled using 1 <;> field_simp <;> ring
  simp only [psi, HermitianMat.mat_add, HermitianMat.mat_smul, sub_neg_eq_add]
  change -t * (holevo Φ + Sᵥₙ τ) + (1 + t) * Real.log (1 + t) ≤
    -OpenAIEntropy.entropy (σ.m + t • τ.m) + OpenAIEntropy.entropy σ.m
  have hself : Sᵥₙ σ = OpenAIEntropy.entropy σ.m := entropy_eq_openai σ
  change Sᵥₙ σ - avgOutputEntropy Φ E = holevo Φ at hE
  linarith

/-- A ratio-free lower bound for the entropy increment at an optimal output
center. The logarithmic normalization correction is bounded below by `t`. -/
theorem optimal_center_entropy_increment_lower_simple (Φ : CPTPMap d e)
    (E : MEnsemble d α) (hE : holevoValue Φ E = holevo Φ) (ρ : MState d)
    {t : ℝ} (ht : 0 < t) :
    t * (1 - holevo Φ - Sᵥₙ (Φ ρ)) ≤
      psi ((Φ (Ensemble.mix E)).M + t • (Φ ρ).M) - psi (Φ (Ensemble.mix E)).M := by
  have hp : 0 < 1 + t := by linarith
  have hlog := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  have he : (1 + t) * (1 - (1 + t)⁻¹) = t := by
    field_simp
    ring
  rw [he] at hlog
  have h := optimal_center_entropy_increment_lower Φ E hE ρ ht
  linarith

end SchurEntropy.Capacity
