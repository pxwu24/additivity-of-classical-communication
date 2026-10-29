import SchurEntropy.RankOne
import Mathlib.Tactic.FieldSimp

noncomputable section

open scoped BigOperators ComplexOrder

namespace SchurEntropy

/-- Normalize a finite complex vector. A zero vector uses the first coordinate
unit vector, so the statement includes zero blocks without a limiting argument. -/
theorem exists_normalized_fin (N : ℕ) (hN : 0 < N) (u : Fin N → ℂ) :
    ∃ v : Fin N → ℂ,
      (∑ a, star (v a) * v a = 1) ∧
      ∀ a, u a = (Real.sqrt (∑ b, Complex.normSq (u b)) : ℂ) * v a := by
  classical
  let r : ℝ := ∑ b, Complex.normSq (u b)
  have hr0 : 0 ≤ r := Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg (u b))
  by_cases hr : r = 0
  · let e : Fin N := ⟨0, hN⟩
    have hu : ∀ a, u a = 0 := by
      intro a
      apply Complex.normSq_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => Complex.normSq_nonneg (u b))).mp hr a (Finset.mem_univ a)
    refine ⟨fun a => if a = e then 1 else 0, ?_, ?_⟩
    · simp [apply_ite]
    · intro a
      have : (∑ b, Complex.normSq (u b)) = 0 := hr
      simp [this, hu a]
  · have hs : (Real.sqrt r : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne hr0 (Ne.symm hr)))
    refine ⟨fun a => u a / (Real.sqrt r : ℂ), ?_, ?_⟩
    · have hnorm : ∑ a, Complex.normSq (u a / (Real.sqrt r : ℂ)) = 1 := by
        simp only [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hr0]
        rw [← Finset.sum_div]
        exact div_self hr
      calc
        (∑ a, star (u a / (Real.sqrt r : ℂ)) * (u a / (Real.sqrt r : ℂ))) =
            ((∑ a, Complex.normSq (u a / (Real.sqrt r : ℂ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          apply Finset.sum_congr rfl
          intro a ha
          exact Complex.normSq_eq_conj_mul_self.symm
        _ = 1 := by rw [hnorm]; simp
    · intro a
      change u a = (Real.sqrt r : ℂ) * (u a / (Real.sqrt r : ℂ))
      field_simp

theorem blockTrace_outerProduct {m : ℕ} {n : Fin m → ℕ}
    (u : BlockIndex n → ℂ) (i : Fin m) :
    blockTrace n (outerProduct u) i = ∑ a : Fin (n i), Complex.normSq (u ⟨i, a⟩) := by
  simp [blockTrace, outerProduct, Complex.mul_conj]

/-- Every rank-one block matrix admits the normalized block vectors used in
the isometric reduction, including when some block traces vanish. -/
theorem exists_block_normalization {m : ℕ} {n : Fin m → ℕ}
    (hn : ∀ i, 0 < n i) (u : BlockIndex n → ℂ) :
    ∃ v : BlockIndex n → ℂ,
      (∀ i : Fin m, ∑ a : Fin (n i), star (v ⟨i, a⟩) * v ⟨i, a⟩ = 1) ∧
      ∀ a : BlockIndex n,
        u a = (Real.sqrt (blockTrace n (outerProduct u) a.1) : ℂ) * v a := by
  classical
  choose v hv hscale using fun i => exists_normalized_fin (n i) (hn i) (fun a => u ⟨i, a⟩)
  refine ⟨fun a => v a.1 a.2, ?_, ?_⟩
  · intro i
    exact hv i
  · intro a
    rw [blockTrace_outerProduct]
    exact hscale a.1 a.2

/-- The normalized columns are an isometry and give the manuscript's
conjugation identity for every scalar Schur coefficient matrix. -/
theorem exists_rankOne_isometry {m : ℕ} {n : Fin m → ℕ}
    (hn : ∀ i, 0 < n i) (u : BlockIndex n → ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) :
    ∃ V : Matrix (BlockIndex n) (Fin m) ℂ,
      V.conjTranspose * V = 1 ∧
      blockSchur C (outerProduct u) =
        V * scalarSkeleton C (blockTrace n (outerProduct u)) * V.conjTranspose := by
  obtain ⟨v, hv, hscale⟩ := exists_block_normalization hn u
  refine ⟨blockColumns v, blockColumns_isometry v hv, ?_⟩
  have hu : u = fun a => (Real.sqrt (blockTrace n (outerProduct u) a.1) : ℂ) * v a :=
    funext hscale
  conv_lhs => rw [hu]
  exact blockSchur_outerProduct_scaled v C (blockTrace n (outerProduct u))

end SchurEntropy
