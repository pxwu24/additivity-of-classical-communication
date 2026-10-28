import SchurEntropy.Capacity.CompactConvexHull
import SchurEntropy.Capacity.Definitions

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Matrix ComplexOrder
open Set

namespace SchurEntropy.Capacity
open QubitAdditivity

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

/-- The output state together with its entropy records everything needed for
an ensemble's Holevo value. -/
def outputEntropyPoint (Φ : CPTPMap d e) (ρ : MState d) : HermitianMat e ℂ × ℝ :=
  ((Φ ρ).M, Sᵥₙ (Φ ρ))

def entropyGraphValue (p : HermitianMat e ℂ × ℝ) : ℝ :=
  (p.1.cfc Real.negMulLog).trace - p.2

theorem continuous_outputEntropyPoint (Φ : CPTPMap d e) :
    Continuous (outputEntropyPoint Φ) := by
  have hΦ : Continuous (fun ρ : MState d => Φ ρ) := map_continuous Φ.toPTPMap
  exact (MState.Continuous_HermitianMat.comp hΦ).prodMk (Sᵥₙ_continuous.comp hΦ)

theorem continuous_entropyGraphValue : Continuous (entropyGraphValue (e := e)) := by
  unfold entropyGraphValue
  fun_prop

theorem graph_sum_fst (Φ : CPTPMap d e) {ι : Type*} [Fintype ι]
    (E : MEnsemble d ι) :
    (∑ i, (E.distr i : ℝ) • outputEntropyPoint Φ (E.states i)).1 =
      (Φ (Ensemble.mix E)).M := by
  rw [Prod.fst_sum]
  simp only [Prod.smul_fst, outputEntropyPoint]
  apply HermitianMat.ext
  rw [channel_mix]
  change (HermitianMat.matₗ (R := ℝ)
    (∑ i, (E.distr i : ℝ) • (Φ (E.states i)).M)) =
    (Ensemble.mix (outputEnsemble Φ E)).m
  rw [map_sum, Ensemble.mix_of]
  simp only [map_smul]
  rfl

theorem entropyGraphValue_sum (Φ : CPTPMap d e) {ι : Type*} [Fintype ι]
    (E : MEnsemble d ι) :
    entropyGraphValue (∑ i, (E.distr i : ℝ) • outputEntropyPoint Φ (E.states i)) =
      holevoValue Φ E := by
  unfold entropyGraphValue holevoValue
  rw [graph_sum_fst]
  rw [Sᵥₙ_eq_trace_cfc_negMulLog]
  simp only [Prod.snd_sum, Prod.smul_snd, outputEntropyPoint, smul_eq_mul]

theorem ensemblePoint_mem_convexHull (Φ : CPTPMap d e) {ι : Type*} [Fintype ι]
    (E : MEnsemble d ι) :
    (∑ i, (E.distr i : ℝ) • outputEntropyPoint Φ (E.states i)) ∈
      convexHull ℝ (Set.range (outputEntropyPoint Φ)) := by
  exact mem_convexHull_of_exists_fintype _ _ (fun _ => Prob.zero_le_coe)
    (ProbDistribution.normalized E.distr) (fun i => Set.mem_range_self _) rfl

theorem convexHull_point_eq_ensemble (Φ : CPTPMap d e)
    {x : HermitianMat e ℂ × ℝ} (hx : x ∈ convexHull ℝ (Set.range (outputEntropyPoint Φ))) :
    ∃ k : ℕ, ∃ E : MEnsemble d (Fin k),
      entropyGraphValue x = holevoValue Φ E := by
  classical
  obtain ⟨ι, hι, w, z, hw, hw1, hz, heq⟩ := mem_convexHull_iff_exists_fintype.mp hx
  let := hι
  choose ρ hρ using hz
  let p : ProbDistribution ι := ProbDistribution.mk' w hw hw1
  let E : MEnsemble d ι := ⟨ρ, p⟩
  let f := Fintype.equivFin ι
  refine ⟨Fintype.card ι, Ensemble.congrMEnsemble f E, ?_⟩
  rw [holevoValue_reindex]
  rw [← entropyGraphValue_sum Φ E]
  congr 1
  rw [← heq]
  apply Finset.sum_congr rfl
  intro i _
  change w i • z i = w i • outputEntropyPoint Φ (ρ i)
  rw [hρ i]

/-- The finite-ensemble Holevo supremum is attained, for every finite-dimensional
channel. Compactness follows from Carathéodory's finite-dimensional bound. -/
theorem exists_optimal_ensemble [Nonempty d] (Φ : CPTPMap d e) :
    ∃ k : ℕ, ∃ E : MEnsemble d (Fin k), holevoValue Φ E = holevo Φ := by
  let K := convexHull ℝ (Set.range (outputEntropyPoint Φ))
  have hc : IsCompact K := isCompact_convexHull
    (isCompact_range (continuous_outputEntropyPoint Φ))
  have hn : K.Nonempty := (Set.range_nonempty _).convexHull
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hn continuous_entropyGraphValue.continuousOn
  obtain ⟨k, E, hE⟩ := convexHull_point_eq_ensemble Φ hx
  refine ⟨k, E, le_antisymm (holevoValue_le_holevo Φ E) ?_⟩
  apply csSup_le (holevoValues_nonempty Φ)
  rintro v ⟨l, F, rfl⟩
  rw [← hE, ← entropyGraphValue_sum Φ F]
  exact hmax (ensemblePoint_mem_convexHull Φ F)

/-- The same attainment statement for the paper's entropy convention in bits. -/
theorem exists_optimalEnsemble [Nonempty d] (Φ : CPTPMap d e) :
    ∃ k : ℕ, ∃ E : MEnsemble d (Fin k), OptimalEnsemble Φ E := by
  obtain ⟨k, E, hE⟩ := exists_optimal_ensemble Φ
  exact ⟨k, E, (optimalEnsemble_iff_nat Φ E).mpr hE⟩

end SchurEntropy.Capacity
