/-
The finite-ensemble mixing construction adapts
KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/UpperBound.lean (Apache-2.0).
The first marginal constraint is replaced by a logarithmic expectation.
See third_party/Apache-2.0.txt and third_party/NOTICE.
-/
import QubitAdditivity.UpperBound
import SchurEntropy.Capacity.LogPairing

noncomputable section
open scoped BigOperators

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {dA eA dB eB α : Type*}
variable [Fintype dA] [DecidableEq dA] [Fintype eA] [DecidableEq eA]
variable [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]
variable [Fintype α]

/-- Real-linear input functional induced by the output-center logarithm. -/
def outputPairingLinear (Φ : CPTPMap dA eA) (σ : MState eA) :
    Matrix dA dA ℂ →ₗ[ℝ] ℝ :=
  (logPairingMatrix σ).comp (Φ.map.restrictScalars ℝ)

@[simp] theorem outputPairingLinear_apply (Φ : CPTPMap dA eA) (σ : MState eA)
    (ρ : MState dA) : outputPairingLinear Φ σ ρ.m = logPairing σ (Φ ρ) := by
  simp [outputPairingLinear, logPairingMatrix, logPairing,
    CPTPMap.mat_coe_eq_apply_mat]

/-- Average natural-log expectation in a finite output ensemble. -/
def meanLogPairing (Φ : CPTPMap dA eA) (σ : MState eA) (E : MEnsemble dA α) : ℝ :=
  ∑ i, (E.distr i : ℝ) * logPairing σ (Φ (E.states i))

theorem meanLogPairing_eq_mix (Φ : CPTPMap dA eA) (σ : MState eA)
    (E : MEnsemble dA α) :
    meanLogPairing Φ σ E = logPairing σ (Φ (Ensemble.mix E)) := by
  rw [← outputPairingLinear_apply, Ensemble.mix_of, map_sum]
  simp [meanLogPairing]

theorem logPairing_traceRight_mix (Φ : CPTPMap dA eA) (σ : MState eA)
    (G : MEnsemble (dA × dB) α) :
    logPairing σ (Φ (Ensemble.mix G).traceRight) =
      ∑ i, (G.distr i : ℝ) * logPairing σ (Φ (G.states i).traceRight) := by
  rw [← outputPairingLinear_apply, traceRight_mix_m, map_sum]
  simp

theorem meanLogPairing_reindex {β : Type*} [Fintype β]
    (Φ : CPTPMap dA eA) (σ : MState eA) (E : MEnsemble dA α) (e : α ≃ β) :
    meanLogPairing Φ σ (Ensemble.congrMEnsemble e E) = meanLogPairing Φ σ E := by
  rw [meanLogPairing_eq_mix, meanLogPairing_eq_mix,
    Ensemble.mix_congrMEnsemble_eq_mix]

/-- The weak splitting condition in natural logarithms. -/
def WeakSplitBelow (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) (ρ : MState (dA × dB)) (s : ℝ) : Prop :=
  ∃ (k l : ℕ) (E : MEnsemble dA (Fin k)) (F : MEnsemble dB (Fin l)),
    meanLogPairing Φ σ E = logPairing σ (Φ ρ.traceRight) ∧
      Ensemble.mix F = ρ.traceLeft ∧ avgOutputEntropy Φ E + avgOutputEntropy Ω F ≤ s

def WeakPureInputBound (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (σ : MState eA) : Prop :=
  ∀ ψ : Ket (dA × dB), WeakSplitBelow Φ Ω σ (MState.pure ψ)
    (Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ)))

def WeakMixedInputBound (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (σ : MState eA) : Prop :=
  ∀ ρ : MState (dA × dB), WeakSplitBelow Φ Ω σ ρ (Sᵥₙ ((Φ ⊗ᶜᵖ Ω) ρ))

theorem weakSplitBelow_mix (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) (G : MEnsemble (dA × dB) α) (s : α → ℝ)
    (h : ∀ i, WeakSplitBelow Φ Ω σ (G.states i) (s i)) :
    WeakSplitBelow Φ Ω σ (Ensemble.mix G) (∑ i, (G.distr i : ℝ) * s i) := by
  classical
  choose k l E F hE hF hs using h
  let eE := Fintype.equivFin (Σ i, Fin (k i))
  let eF := Fintype.equivFin (Σ i, Fin (l i))
  refine ⟨Fintype.card (Σ i, Fin (k i)), Fintype.card (Σ i, Fin (l i)),
    Ensemble.congrMEnsemble eE (sigmaEnsemble G.distr E),
    Ensemble.congrMEnsemble eF (sigmaEnsemble G.distr F), ?_, ?_, ?_⟩
  · rw [meanLogPairing_reindex]
    change (∑ x, ((sigmaEnsemble G.distr E).distr x : ℝ) *
      logPairing σ (Φ ((sigmaEnsemble G.distr E).states x))) = _
    rw [sigmaEnsemble_sum G.distr E (fun ρ => logPairing σ (Φ ρ))]
    change (∑ i, (G.distr i : ℝ) * meanLogPairing Φ σ (E i)) = _
    simp only [hE]
    exact (logPairing_traceRight_mix Φ σ G).symm
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    apply MState.ext_m
    rw [sigmaEnsemble_mix, traceLeft_mix_m]
    simp only [hF]
  · rw [avgOutputEntropy_reindex, avgOutputEntropy_reindex]
    unfold avgOutputEntropy
    rw [sigmaEnsemble_sum G.distr E (fun ρ => Sᵥₙ (Φ ρ)),
      sigmaEnsemble_sum G.distr F (fun ρ => Sᵥₙ (Ω ρ)), ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hs i) Prob.zero_le_coe

theorem weakMixedInputBound_of_pure (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) (h : WeakPureInputBound Φ Ω σ) : WeakMixedInputBound Φ Ω σ := by
  intro ρ
  let G : MEnsemble (dA × dB) (dA × dB) := ↑(Ensemble.spectral_ensemble ρ)
  have hmix : Ensemble.mix G = ρ := Ensemble.spectral_ensemble_mix
  have hsplit := weakSplitBelow_mix Φ Ω σ G (fun i => Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (G.states i)))
    (fun i => h ((Ensemble.spectral_ensemble ρ).states i))
  rw [hmix] at hsplit
  obtain ⟨k, l, E, F, hE, hF, hs⟩ := hsplit
  refine ⟨k, l, E, F, hE, hF, hs.trans ?_⟩
  have hc := entropy_mix_ge (outputEnsemble (Φ ⊗ᶜᵖ Ω) G)
  rw [← channel_mix, hmix] at hc
  exact hc

theorem mean_centerGap_le (Φ : CPTPMap dA eA) (σ : MState eA)
    (hRadius : ∀ ρ : MState dA, -Sᵥₙ (Φ ρ) - logPairing σ (Φ ρ) ≤ holevo Φ)
    (E : MEnsemble dA α) :
    -avgOutputEntropy Φ E - meanLogPairing Φ σ E ≤ holevo Φ := by
  have hi := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset α)) =>
    mul_le_mul_of_nonneg_left (hRadius (E.states i)) (Prob.zero_le_coe (p := E.distr i)))
  simpa [avgOutputEntropy, meanLogPairing, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ProbDistribution.normalized] using hi

/-- The weak criterion's finite-ensemble argument. The two center bounds here
are proved from actual optimality in the output-center modules. -/
theorem weak_holevoValue_prod_le (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (σ : MState eA) (h : WeakMixedInputBound Φ Ω σ)
    (hGibbs : ∀ ρ : MState dA, Sᵥₙ (Φ ρ) + logPairing σ (Φ ρ) ≤ 0)
    (hRadius : ∀ ρ : MState dA, -Sᵥₙ (Φ ρ) - logPairing σ (Φ ρ) ≤ holevo Φ)
    {k : ℕ} (G : MEnsemble (dA × dB) (Fin k)) :
    holevoValue (Φ ⊗ᶜᵖ Ω) G ≤ holevo Φ + holevo Ω := by
  obtain ⟨k₁, l₁, E, F, hE, hF, hs⟩ := weakSplitBelow_mix Φ Ω σ G
    (fun i => Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (G.states i))) (fun i => h (G.states i))
  have hsub := entropy_prod_channel_le Φ Ω (Ensemble.mix G)
  have hA := mean_centerGap_le Φ σ hRadius E
  have hg := hGibbs (Ensemble.mix G).traceRight
  have hB := holevoValue_le_holevo Ω F
  rw [holevoValue_eq, hF] at hB
  rw [hE] at hA
  rw [holevoValue_eq]
  change avgOutputEntropy Φ E + avgOutputEntropy Ω F ≤
    avgOutputEntropy (Φ ⊗ᶜᵖ Ω) G at hs
  linarith

/-- Conditional algebraic assembly; the final exported criterion discharges
the Gibbs and center-radius facts using optimality of an actual ensemble. -/
theorem holevo_prod_eq_of_weak_and_center_bounds [Nonempty dA] [Nonempty dB]
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (σ : MState eA)
    (h : WeakPureInputBound Φ Ω σ)
    (hGibbs : ∀ ρ : MState dA, Sᵥₙ (Φ ρ) + logPairing σ (Φ ρ) ≤ 0)
    (hRadius : ∀ ρ : MState dA, -Sᵥₙ (Φ ρ) - logPairing σ (Φ ρ) ≤ holevo Φ) :
    holevo (Φ ⊗ᶜᵖ Ω) = holevo Φ + holevo Ω := by
  apply le_antisymm _ (holevo_product_ge Φ Ω)
  apply csSup_le (holevoValues_nonempty _)
  rintro v ⟨k, G, rfl⟩
  exact weak_holevoValue_prod_le Φ Ω σ (weakMixedInputBound_of_pure Φ Ω σ h)
    hGibbs hRadius G

end SchurEntropy.Capacity
