import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp

noncomputable section
open scoped BigOperators
open Set

namespace SchurEntropy.Capacity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def finiteCombinations (s : Set E) (k : ℕ) : Set E :=
  (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
    ({w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} ×ˢ
      Set.pi Set.univ (fun _ : Fin k => s))

theorem isCompact_finiteCombinations {s : Set E} (hs : IsCompact s) (k : ℕ) :
    IsCompact (finiteCombinations s k) := by
  have hw : IsCompact {w : Fin k → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
    have hc := isCompact_range (show Continuous
      (fun t : Convexity.StdSimplex ℝ (Fin k) => (t.weights : Fin k → ℝ)) by fun_prop)
    rw [Convexity.StdSimplex.range_toFun_comp_weights] at hc
    convert hc using 1
    ext w
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  apply (hw.prod (isCompact_univ_pi (fun _ => hs))).image
  fun_prop

theorem finiteCombinations_subset_convexHull (s : Set E) (k : ℕ) :
    finiteCombinations s k ⊆ convexHull ℝ s := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact mem_convexHull_of_exists_fintype w z hw.1 hw.2 (fun i => hz i (mem_univ i)) rfl

variable [FiniteDimensional ℝ E]

theorem convexHull_eq_bounded_combinations (s : Set E) :
    convexHull ℝ s = ⋃ k : Fin (Module.finrank ℝ E + 2), finiteCombinations s k.val := by
  classical
  apply Subset.antisymm
  · intro x hx
    let t := Caratheodory.minCardFinsetOfMemConvexHull hx
    have ht : (t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
    have hi : AffineIndependent ℝ ((↑) : t → E) :=
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
    have hc : Fintype.card t ≤ Module.finrank ℝ E + 1 :=
      hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    have hx' : x ∈ convexHull ℝ (t : Set E) :=
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx
    rw [Finset.convexHull_eq] at hx'
    obtain ⟨w, hw, hw1, hsum⟩ := hx'
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hsum
    let e := Fintype.equivFin t
    let k : Fin (Module.finrank ℝ E + 2) := ⟨Fintype.card t, by omega⟩
    refine mem_iUnion.mpr ⟨k, ?_⟩
    refine ⟨⟨fun i => w (e.symm i), fun i => (e.symm i : E)⟩, ⟨?_, ?_⟩, ?_⟩
    · constructor
      · intro i
        exact hw _ (e.symm i).property
      · change ∑ i : Fin (Fintype.card t), w (e.symm i) = 1
        rw [e.symm.sum_comp (fun j : t => w j)]
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw1
    · intro i _
      exact ht (e.symm i).property
    · change (∑ i : Fin (Fintype.card t), w (e.symm i) • (e.symm i : E)) = x
      rw [e.symm.sum_comp (fun j : t => w j • (j : E))]
      change (∑ i ∈ t.attach, w (i : E) • (i : E)) = x
      rw [Finset.sum_attach t (fun j => w j • j)]
      simpa only [id_eq] using hsum
  · exact iUnion_subset fun k => finiteCombinations_subset_convexHull s k.val

/-- In a finite-dimensional real normed space, a compact set has compact convex hull. -/
theorem isCompact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rw [convexHull_eq_bounded_combinations]
  exact isCompact_iUnion (fun k => isCompact_finiteCombinations hs k.val)

end SchurEntropy.Capacity
