import SchurEntropy.Definitions
import SchurEntropy.Reduction
import SchurEntropy.SpectralDecomposition
import SchurEntropy.RankOneInequality

/-!
# Matrix instantiation of the conditional reduction

This file uses the genuine spectral entropy from `Definitions`. It proves the
displayed block-entropy inequality **conditional on** the two analytic lemmas,
the rank-one comparison, a finite rank-one decomposition, and a supporting
linear functional at the scalar trace parameters. It is not an unconditional
proof of `BlockEntropyStatement`.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy

def blockSchurLinear {m : ℕ} {n : Fin m → ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) : BlockMatrix n →ₗ[ℝ] BlockMatrix n where
  toFun := blockSchur C
  map_add' := blockSchur_add C
  map_smul' := blockSchur_smul C

def blockTraceLinear {m : ℕ} (n : Fin m → ℕ) :
    BlockMatrix n →ₗ[ℝ] (Fin m → ℝ) where
  toFun := blockTrace n
  map_add' := blockTrace_add n
  map_smul' := blockTrace_smul n

def dotLinear {m : ℕ} (μ : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun := dot μ
  map_add' := by
    intro x y
    simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro t y
    simp [dot, Finset.mul_sum, mul_left_comm]

/-- The actual block-entropy conclusion, with all unproved analytic inputs
visible as hypotheses. The rank-one input is restricted to outer products
`vecMulVec u (star u)`, rather than arbitrary positive matrices.
-/
theorem blockEntropy_of_analytic_inputs_and_decomposition
    (hOptimized : OptimizedConcavityStatement)
    (hScalar : ScalarConvexityStatement)
    {m : ℕ} (n : Fin m → ℕ)
    (hm : 0 < m) (hn : ∀ i, 0 < n i)
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.PosSemidef)
    (H W : BlockMatrix n) (hH : H.PosSemidef)
    (hW : W ∈ admissibleNoise n)
    {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1)
    (u : α → BlockIndex n → ℂ)
    (hdecomp : ∑ a ∈ s, p a • Matrix.vecMulVec (u a) (star (u a)) = H)
    (μ : Fin m → ℝ) (hμ : ∀ i, μ i < 0)
    (hRankOne : ∀ (v : BlockIndex n → ℂ) (V : BlockMatrix n),
      V ∈ admissibleNoise n →
      scalarFunction C (blockTrace n (Matrix.vecMulVec v (star v)))
        (blockTrace n V) ≤
      deficit n (blockSchur C (Matrix.vecMulVec v (star v))) V)
    (hSupport : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
      scalarFunction C (blockTrace n H) (blockTrace n W) +
        dot μ (z - blockTrace n W) ≤
      scalarFunction C (blockTrace n H) z) :
    scalarFunction C (blockTrace n H) (blockTrace n W) ≤
      deficit n (blockSchur C H) W := by
  classical
  obtain ⟨hmin, hg⟩ := hOptimized m n μ hm hn hμ
  have houter (a : α) : (Matrix.vecMulVec (u a) (star (u a))).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (u a)
  have hpart (a : α) :
      (blockSchur C (Matrix.vecMulVec (u a) (star (u a)))).PosSemidef :=
    blockSchur_posSemidef hC (houter a)
  choose V hV hvalue hminimal using fun a =>
    hmin (blockSchur C (Matrix.vecMulVec (u a) (star (u a)))) (hpart a)
  have hSchurSum :
      (∑ a ∈ s, p a • blockSchur C (Matrix.vecMulVec (u a) (star (u a)))) =
        blockSchur C H := by
    simpa [blockSchurLinear] using
      congrArg (blockSchurLinear (n := n) C) hdecomp
  have hTraceSum :
      (∑ a ∈ s, p a • blockTrace n (Matrix.vecMulVec (u a) (star (u a)))) =
        blockTrace n H := by
    simpa [blockTraceLinear] using
      congrArg (blockTraceLinear n) hdecomp
  have hlower : optimizedDeficit n μ (blockSchur C H) ≤
      deficit n (blockSchur C H) W - dot μ (blockTrace n W) := by
    obtain ⟨Z, hZ, hZvalue, hZmin⟩ := hmin (blockSchur C H)
      (blockSchur_posSemidef hC hH)
    rw [hZvalue]
    simpa only [dualCost_eq] using hZmin W hW
  have hcomponent (a : α) :
      scalarFunction C (blockTrace n (Matrix.vecMulVec (u a) (star (u a))))
        (blockTrace n (V a)) - dot μ (blockTrace n (V a)) ≤
      optimizedDeficit n μ (blockSchur C (Matrix.vecMulVec (u a) (star (u a)))) := by
    rw [hvalue a, dualCost_eq]
    exact sub_le_sub_right (hRankOne (u a) (V a) (hV a)) _
  have hnonneg : ∀ i, 0 ≤ (∑ a ∈ s, p a • blockTrace n (V a)) i := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg fun a ha =>
      mul_nonneg (hp a ha) (blockTrace_nonneg n (hV a).1 i)
  exact blockEntropy_of_concave_convex_reduction s p hp hs
    (fun a => blockSchur C (Matrix.vecMulVec (u a) (star (u a))))
    (fun a => blockTrace n (Matrix.vecMulVec (u a) (star (u a))))
    (fun a => blockTrace n (V a))
    (blockSchur C H) (blockTrace n H) (blockTrace n W)
    hSchurSum hTraceSum
    {J : BlockMatrix n | J.PosSemidef}
    {q : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ q.1 i) ∧ (∀ i, 0 ≤ q.2 i)}
    (fun a _ => hpart a)
    (fun a _ => ⟨blockTrace_nonneg n (houter a), blockTrace_nonneg n (hV a).1⟩)
    (optimizedDeficit n μ) (fun q => scalarFunction C q.1 q.2) (dotLinear μ)
    hg (hScalar m C hm hC) (deficit n (blockSchur C H) W)
    hlower (fun a _ => hcomponent a) (hSupport _ hnonneg)

/-- The conditional matrix theorem with the finite rank-one decomposition
discharged by the proved uniform decomposition of a positive matrix.

The two analytic lemmas and negative supporting functional are explicit
hypotheses. The rank-one comparison is supplied by `rankOne_block_entropy`.
-/
theorem blockEntropy_of_analytic_inputs
    (hOptimized : OptimizedConcavityStatement)
    (hScalar : ScalarConvexityStatement)
    {m : ℕ} (n : Fin m → ℕ)
    (hm : 0 < m) (hn : ∀ i, 0 < n i)
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.PosSemidef)
    (H W : BlockMatrix n) (hH : H.PosSemidef)
    (hW : W ∈ admissibleNoise n)
    (μ : Fin m → ℝ) (hμ : ∀ i, μ i < 0)
    (hSupport : ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
      scalarFunction C (blockTrace n H) (blockTrace n W) +
        dot μ (z - blockTrace n W) ≤
      scalarFunction C (blockTrace n H) z) :
    scalarFunction C (blockTrace n H) (blockTrace n W) ≤
      deficit n (blockSchur C H) W := by
  let : Nonempty (BlockIndex n) := ⟨⟨⟨0, hm⟩, ⟨0, hn ⟨0, hm⟩⟩⟩⟩
  obtain ⟨u, hu⟩ := exists_uniform_rankOne_decomposition H hH
  exact blockEntropy_of_analytic_inputs_and_decomposition hOptimized hScalar
    n hm hn C hC H W hH hW Finset.univ
    (fun _ : BlockIndex n => 1 / (Fintype.card (BlockIndex n) : ℝ))
    (fun _ _ => uniform_rankOne_weights_pos.le)
    (by simpa using (uniform_rankOne_weights_sum (ι := BlockIndex n)))
    u (by simpa using hu) μ hμ
    (fun v V hV => by
      have he : SchurEntropy.outerProduct v = Matrix.vecMulVec v (star v) := by
        ext a b
        rfl
      rw [← he]
      exact rankOne_block_entropy hn C hC v V hV.1 hV.2)
    hSupport

end SchurEntropy
