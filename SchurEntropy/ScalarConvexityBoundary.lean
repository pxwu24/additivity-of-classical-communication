import SchurEntropy.BlockBoundary

/-! Continuous extension of scalar joint convexity to zero weights. -/

noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator

namespace SchurEntropy

/-- Nonnegative trace-vector pairs form a convex set. -/
theorem convex_nonnegativePairs (m : ℕ) :
    Convex ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ p.2 i)} := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x.1 i + b * y.1 i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · intro i
    change 0 ≤ a * x.2 i + b * y.2 i
    exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hb (hy.2 i))

/-- For a fixed positive semidefinite `C`, convexity for strictly positive
weights extends to all nonnegative weights by continuity of matrix entropy. -/
theorem scalarConvexity_boundary {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : C.PosSemidef)
    (hInterior : ConvexOn ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i)}
      (fun p => scalarFunction C p.1 p.2)) :
    ConvexOn ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ p.2 i)}
      (fun p => scalarFunction C p.1 p.2) := by
  refine ⟨convex_nonnegativePairs m, ?_⟩
  intro x hx y hy a b ha hb hab
  let xp (t : ℝ) : (Fin m → ℝ) × (Fin m → ℝ) :=
    (fun i => x.1 i + t, fun i => x.2 i + t)
  let yp (t : ℝ) : (Fin m → ℝ) × (Fin m → ℝ) :=
    (fun i => y.1 i + t, fun i => y.2 i + t)
  have hxp : Continuous xp := by unfold xp; fun_prop
  have hyp : Continuous yp := by unfold yp; fun_prop
  have hmix : Continuous (fun t => a • xp t + b • yp t) := by fun_prop
  have hleft := continuous_scalarFunction_family (fun _ : ℝ => C)
    (fun t => (a • xp t + b • yp t).1) (fun t => (a • xp t + b • yp t).2)
    continuous_const hmix.fst hmix.snd (fun _ => hC.isHermitian)
  have hxval := continuous_scalarFunction_family (fun _ : ℝ => C)
    (fun t => (xp t).1) (fun t => (xp t).2)
    continuous_const hxp.fst hxp.snd (fun _ => hC.isHermitian)
  have hyval := continuous_scalarFunction_family (fun _ : ℝ => C)
    (fun t => (yp t).1) (fun t => (yp t).2)
    continuous_const hyp.fst hyp.snd (fun _ => hC.isHermitian)
  have hright : Continuous (fun t => a * scalarFunction C (xp t).1 (xp t).2 +
      b * scalarFunction C (yp t).1 (yp t).2) :=
    (continuous_const.mul hxval).add (continuous_const.mul hyval)
  have hl : Tendsto (fun t => scalarFunction C (a • xp t + b • yp t).1
      (a • xp t + b • yp t).2) (𝓝[>] 0)
      (𝓝 (scalarFunction C (a • x + b • y).1 (a • x + b • y).2)) := by
    simpa [xp, yp] using (hleft.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun t => a * scalarFunction C (xp t).1 (xp t).2 +
      b * scalarFunction C (yp t).1 (yp t).2) (𝓝[>] 0)
      (𝓝 (a * scalarFunction C x.1 x.2 + b * scalarFunction C y.1 y.2)) := by
    simpa [xp, yp] using (hright.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply hInterior.2
  · exact ⟨fun i => add_pos_of_nonneg_of_pos (hx.1 i) ht,
      fun i => add_pos_of_nonneg_of_pos (hx.2 i) ht⟩
  · exact ⟨fun i => add_pos_of_nonneg_of_pos (hy.1 i) ht,
      fun i => add_pos_of_nonneg_of_pos (hy.2 i) ht⟩
  · exact ha
  · exact hb
  · exact hab

/-- The full scalar convexity statement reduces to strictly positive weights;
positive semidefinite coefficients and zero boundary weights are retained. -/
theorem scalarConvexity_of_positive
    (hInterior : ∀ (m : ℕ) (C : Matrix (Fin m) (Fin m) ℂ),
      0 < m → C.PosSemidef →
      ConvexOn ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
        (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2 i)}
        (fun p => scalarFunction C p.1 p.2)) : ScalarConvexityStatement := by
  intro m C hm hC
  exact scalarConvexity_boundary C hC (hInterior m C hm hC)

end SchurEntropy
