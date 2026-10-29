import SchurEntropy.OptimizedInterior

/-!
# Strict convexity of the optimized-noise objective

Adapted to arbitrary finite blocks from `QubitAdditivity/BetaDualConvex.lean`
in KitaKen1/qubit-strong-additivity at commit
`90e61c463deb42067c109c46f048c6374dfc5945` (Apache-2.0):
https://github.com/KitaKen1/qubit-strong-additivity/blob/90e61c463deb42067c109c46f048c6374dfc5945/lean/QubitAdditivity/BetaDualConvex.lean
See `third_party/NOTICE` and `third_party/Apache-2.0.txt`.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace SchurEntropy.Optimized
open QubitAdditivity

@[reducible] private local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] private local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] private local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule

variable {m : ℕ} {n : Fin m → ℕ}

theorem convex_positiveInterior : Convex ℝ (positiveInterior (n := n)) := by
  intro W hW Z hZ a b ha hb hab i
  exact BetaDualConvex.posDef_convex_combination (hW i) (hZ i) ha hb hab

theorem hasDerivAt_objective_line {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    (W H : Blocks n) {t : ℝ} (hW : line W H t ∈ positiveInterior)
    (hT : (J+diagonal (line W H t)).mat.PosDef) :
    HasDerivAt (fun u : ℝ => objective J lambda (line W H u))
      (gradient J lambda (line W H t) H) t := by
  convert! (hasFDerivAt_objective lambda hW hT).comp_hasDerivAt t
    (hasDerivAt_line W H t) using 1

theorem hasDerivAt_deriv_objective_line {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    (W H : Blocks n) {t : ℝ} (hW : line W H t ∈ positiveInterior)
    (hT : (J+diagonal (line W H t)).mat.PosDef) :
    HasDerivAt (deriv (fun u : ℝ => objective J lambda (line W H u)))
      (hessianRow J (line W H t) H H) t := by
  have hd : HasDerivAt (fun u : ℝ => gradient J lambda (line W H u) H)
      (hessianRow J (line W H t) H H) t := by
    convert! (hasFDerivAt_gradient_row lambda hW hT H).comp_hasDerivAt t
      (hasDerivAt_line W H t) using 1
  have hw : ∀ᶠ u : ℝ in 𝓝 t, line W H u ∈ positiveInterior :=
    (continuous_line W H).tendsto t |>.eventually (positiveInterior_mem_nhds hW)
  have hc : Continuous (fun u : ℝ => J+diagonal (line W H u)) := by
    convert! continuous_const.add ((diagonalCLM (n := n)).continuous.comp
      (continuous_line W H)) using 1
  have ht : ∀ᶠ u : ℝ in 𝓝 t, (J+diagonal (line W H u)).mat.PosDef :=
    (hc.tendsto t).eventually (BetaLog.eventually_posDef hT)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hw,ht] with u huw hut
  exact (hasDerivAt_objective_line lambda W H huw hut).deriv

theorem line_mem_positiveInterior {W Z : Blocks n} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    line W (Z-W) t ∈ positiveInterior := by
  have he : line W (Z-W) t = (1-t) • W+t • Z := by unfold line; module
  rw [he]
  exact convex_positiveInterior hW hZ (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem strictConvexOn_objective_line {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    (hJ : J.mat.PosDef) {W Z : Blocks n} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) (hne : W ≠ Z) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t : ℝ => objective J lambda (line W (Z-W) t)) := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := line_mem_positiveInterior hW hZ ht
  have hn : Z-W ≠ 0 := sub_ne_zero.mpr hne.symm
  apply strictConvexOn_of_deriv2_pos' (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_objective_line lambda W (Z-W) (hp t ht)
      (total_posDef hJ (interior_subset_cone (hp t ht)))).continuousAt.continuousWithinAt
  · intro t ht
    change 0 < deriv (deriv (fun u : ℝ => objective J lambda (line W (Z-W) u))) t
    rw [(hasDerivAt_deriv_objective_line lambda W (Z-W) (hp t ht)
      (total_posDef hJ (interior_subset_cone (hp t ht)))).deriv]
    exact hessianRow_self_pos hJ (hp t ht) hn

theorem strictConvexOn_objective {J : HermitianMat (BlockIndex n) ℂ} (lambda : Fin m → ℝ)
    (hJ : J.mat.PosDef) : StrictConvexOn ℝ positiveInterior (objective J lambda) := by
  refine ⟨convex_positiveInterior,?_⟩
  intro W hW Z hZ hne a b ha hb hab
  have hs := strictConvexOn_objective_line lambda hJ hW hZ hne
  have hi := hs.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have he : line W (Z-W) (a • (0 : ℝ)+b • (1 : ℝ)) = a • W+b • Z := by
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add,line]
    have hh : 1-b = a := by linarith
    calc
      W+b • (Z-W) = (1-b) • W+b • Z := by module
      _ = _ := by rw [hh]
  have h₀ : line W (Z-W) 0 = W := by simp [line]
  have h₁ : line W (Z-W) 1 = Z := by simp [line]
  simpa only [he,h₀,h₁] using hi

theorem eq_of_minOn_positiveCone {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) {W Z : Blocks n} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) (hw : IsMinOn (objective J lambda) positiveCone W)
    (hz : IsMinOn (objective J lambda) positiveCone Z) : W = Z := by
  apply (strictConvexOn_objective lambda hJ).eq_of_isMinOn
    (fun U hu => hw (interior_subset_cone hu))
    (fun U hu => hz (interior_subset_cone hu)) hW hZ

theorem existsUnique_minOn_positiveCone {J : HermitianMat (BlockIndex n) ℂ} {lambda : Fin m → ℝ}
    (hJ : J.mat.PosDef) (hl : ∀ i, lambda i < 0) :
    ∃! W : Blocks n, W ∈ positiveCone ∧ IsMinOn (objective J lambda) positiveCone W := by
  obtain ⟨W,hW,hmin⟩ := exists_minOn_positiveCone hJ hl
  refine ⟨W,⟨hW,hmin⟩,?_⟩
  intro Z hZ
  exact eq_of_minOn_positiveCone hJ (positiveInterior_of_minOn hJ hZ.1 hZ.2)
    (positiveInterior_of_minOn hJ hW hmin) hZ.2 hmin

end SchurEntropy.Optimized
