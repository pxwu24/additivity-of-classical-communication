import Mathlib.Analysis.Convex.Jensen
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional convex-combination reduction

This file verifies the finite-dimensional convex-combination argument in the
proof of the block entropy inequality. It does **not** establish the analytic
entropy inequalities. Concavity, convexity, the rank-one comparison, and the
supporting-plane inequality are explicit hypotheses of the theorem below.

The intended substitutions are:
* `g` is the optimized entropy deficit `Ĝ_Λ`;
* `f` is the scalar entropy deficit `f_C`;
* `L` is the linear functional `y ↦ μ · y`;
* `δ` is the block entropy deficit `Δ(J,W)`;
* `(x i, r i, y i)` are the rank-one component and the traces of its blocks
  and of an attained minimizing perturbation.
-/

namespace SchurEntropy

open scoped BigOperators

section ConditionalReduction

variable {ι X R Y : Type*}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup R] [Module ℝ R]
variable [AddCommGroup Y] [Module ℝ Y]

/-- The convex-combination reduction in the block-entropy proof.

This is a conditional theorem: in particular, `hg` and `hf` are the two
analytic concavity/convexity inputs, not conclusions established by this file.
The hypothesis `hcomponent` is the rank-one estimate at an attained minimizer.
-/
theorem blockEntropy_of_concave_convex_reduction
    (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hs : ∑ i ∈ s, p i = 1)
    (x : ι → X) (r : ι → R) (y : ι → Y)
    (x₀ : X) (r₀ : R) (y₀ : Y)
    (hx₀ : ∑ i ∈ s, p i • x i = x₀)
    (hr₀ : ∑ i ∈ s, p i • r i = r₀)
    (SX : Set X) (SRY : Set (R × Y))
    (hx : ∀ i ∈ s, x i ∈ SX)
    (hry : ∀ i ∈ s, (r i, y i) ∈ SRY)
    (g : X → ℝ) (f : R × Y → ℝ) (L : Y →ₗ[ℝ] ℝ)
    (hg : ConcaveOn ℝ SX g) (hf : ConvexOn ℝ SRY f)
    (δ : ℝ)
    (hlower : g x₀ ≤ δ - L y₀)
    (hcomponent : ∀ i ∈ s, f (r i, y i) - L (y i) ≤ g (x i))
    (hsupport : f (r₀, y₀) + L ((∑ i ∈ s, p i • y i) - y₀) ≤
      f (r₀, ∑ i ∈ s, p i • y i)) :
    f (r₀, y₀) ≤ δ := by
  have hconcave := hg.le_map_sum hp hs hx
  rw [hx₀] at hconcave
  have hpair : (∑ i ∈ s, p i • (r i, y i)) =
      (r₀, ∑ i ∈ s, p i • y i) := by
    ext
    · simpa only [Prod.fst_sum, Prod.smul_fst] using hr₀
    · simp only [Prod.snd_sum, Prod.smul_snd]
  have hconvex := hf.map_sum_le hp hs hry
  rw [hpair] at hconvex
  have hsum : (∑ i ∈ s, p i * (f (r i, y i) - L (y i))) ≤
      ∑ i ∈ s, p i * g (x i) := by
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (hcomponent i hi) (hp i hi)
  have hlinear : L (∑ i ∈ s, p i • y i) =
      ∑ i ∈ s, p i * L (y i) := by
    simp only [map_sum, map_smul, smul_eq_mul]
  simp only [smul_eq_mul] at hconcave hconvex
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  rw [map_sub, hlinear] at hsupport
  linarith

end ConditionalReduction

end SchurEntropy
