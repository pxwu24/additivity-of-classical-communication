import SchurEntropy.Capacity.GibbsMatrix
import SchurEntropy.Capacity.LogPairing
import QubitAdditivity.Entropy

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace SchurEntropy.Capacity.Gibbs
open QubitAdditivity QubitAdditivity.BetaEntropy
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A state version of the regularized Gibbs inequality. The error tends to
zero and no support inclusion is assumed for the regularized logarithm. -/
theorem regularized_gibbs (σ ρ : MState d) {t : ℝ} (ht : 0 < t) :
    Sᵥₙ ρ + (ρ.m * BetaPowers.logarithm (σ.m + t • (1 : Matrix d d ℂ))).trace.re ≤
      t * Fintype.card d := by
  let Y : HermitianMat d ℂ := σ.M + t • 1
  have hY : Y.mat.PosDef := by
    change (σ.m + t • (1 : Matrix d d ℂ)).PosDef
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) ht).add_posSemidef σ.psd
  have hi := entropy_log_le_trace_sub (X := ρ.M) (Y := Y) ρ.psd hY
  change OpenAIEntropy.entropy ρ.m +
    (ρ.m * BetaPowers.logarithm (σ.m + t • (1 : Matrix d d ℂ))).trace.re ≤
    Y.mat.trace.re - ρ.m.trace.re at hi
  rw [← entropy_eq_openai ρ] at hi
  have htr : Y.mat.trace.re - ρ.m.trace.re = t * Fintype.card d := by
    simp [Y, Matrix.trace_add, Matrix.trace_smul, MState.tr']
  rw [htr] at hi
  exact hi

/-- Passing the regularized Gibbs inequality to a finite logarithmic pairing
limit gives the support-sensitive entropy bound at a singular center. -/
theorem gibbs_of_regularized_limit (σ ρ : MState d)
    (hlimit : Tendsto
      (fun t : ℝ => (ρ.m * BetaPowers.logarithm (σ.m + t • (1 : Matrix d d ℂ))).trace.re)
      (𝓝[>] 0) (𝓝 (logPairing σ ρ))) :
    Sᵥₙ ρ + logPairing σ ρ ≤ 0 := by
  have hleft : Tendsto
      (fun t : ℝ => Sᵥₙ ρ +
        (ρ.m * BetaPowers.logarithm (σ.m + t • (1 : Matrix d d ℂ))).trace.re)
      (𝓝[>] 0) (𝓝 (Sᵥₙ ρ + logPairing σ ρ)) :=
    tendsto_const_nhds.add hlimit
  have hright : Tendsto (fun t : ℝ => t * (Fintype.card d : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t * (Fintype.card d : ℝ)) := by fun_prop
    simpa only [zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact regularized_gibbs σ ρ ht

end SchurEntropy.Capacity.Gibbs
