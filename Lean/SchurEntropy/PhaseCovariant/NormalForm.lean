import SchurEntropy.PhaseCovariant.CharacterSupport

/-! # The fixed-basis phase-covariant normal form

The Schur matrix is a principal submatrix of the channel's Choi matrix, while
the stochastic coefficients are its nonnegative diagonal entries.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Coefficients on the coherent matrix units. -/
def schurCoefficients (Φ : CPTPMap d d) : Matrix d d ℂ :=
  fun i j => Φ.map (Matrix.single i j 1) i j

/-- Classical transition coefficients in the fixed basis. -/
def transitionCoefficients (Φ : CPTPMap d d) : Matrix d d ℝ :=
  fun i j => (Φ.map (Matrix.single j j 1) i i).re

lemma schurCoefficients_psd (Φ : CPTPMap d d) : (schurCoefficients Φ).PosSemidef := by
  exact Φ.choi_PSD_of_CPTP.submatrix (fun i : d => (i, i))

lemma transitionCoefficient_complex_nonneg (Φ : CPTPMap d d) (i j : d) :
    0 ≤ Φ.map (Matrix.single j j 1) i i := by
  exact Φ.choi_PSD_of_CPTP.diag_nonneg (i := (i, j))

lemma transitionCoefficients_nonneg (Φ : CPTPMap d d) (i j : d) :
    0 ≤ transitionCoefficients Φ i j := by
  exact (Complex.nonneg_iff.mp (transitionCoefficient_complex_nonneg Φ i j)).1

lemma transitionCoefficients_cast (Φ : CPTPMap d d) (i j : d) :
    (transitionCoefficients Φ i j : ℂ) = Φ.map (Matrix.single j j 1) i i := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (transitionCoefficient_complex_nonneg Φ i j)).2

lemma transitionCoefficients_colsum (Φ : CPTPMap d d) (j : d) :
    ∑ i, transitionCoefficients Φ i j = 1 := by
  have h := congrArg Complex.re (Φ.TP (Matrix.single j j 1))
  simpa [Matrix.trace, Matrix.diag, transitionCoefficients, Matrix.single] using h

lemma schurCoefficients_diag (Φ : CPTPMap d d) (i : d) :
    schurCoefficients Φ i i = (transitionCoefficients Φ i i : ℂ) :=
  (transitionCoefficients_cast Φ i i).symm

/-- Exact coefficients of matrix units after character separation. -/
lemma phase_matrixUnit_entries (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (a b k l : d) :
    Φ.map (Matrix.single a b 1) k l =
      if k = l then
        if a = b then (transitionCoefficients Φ k a : ℂ) else 0
      else if a = k ∧ b = l then schurCoefficients Φ k l else 0 := by
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    by_cases hab : a = b
    · subst b
      simp [transitionCoefficients_cast]
    · simp only [hab, ite_false]
      apply phase_matrixUnit_offdiag_support Φ h a b k k hab
      by_cases hka : k = a
      · subst k
        exact Or.inr hab
      · exact Or.inl hka
  · simp only [hkl, ite_false]
    by_cases hab : a = b
    · subst b
      rw [phase_matrixUnit_diag_support Φ h a k l hkl]
      have hbad : ¬ (a = k ∧ a = l) := by rintro ⟨rfl, rfl⟩; exact hkl rfl
      simp [hbad]
    · by_cases hp : a = k ∧ b = l
      · rcases hp with ⟨rfl, rfl⟩
        simp [schurCoefficients]
      · rw [phase_matrixUnit_offdiag_support Φ h a b k l hab
          (by tauto)]
        simp [hp]

/-- Reconstructing a linear map from its matrix-unit images. -/
lemma matrixMap_entry_expansion (Φ : CPTPMap d d) (X : Matrix d d ℂ) (k l : d) :
    Φ.map X k l = ∑ a, ∑ b, X a b * Φ.map (Matrix.single a b 1) k l := by
  have h := congrArg (fun M : MatrixMap d d ℂ => M X k l)
    (MatrixMap.choi_map_inv Φ.map)
  exact h.symm

/-- Covariance determines the full Schur-plus-classical action. -/
lemma phaseCovariant_action (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (X : Matrix d d ℂ) :
    Φ.map X = (schurCoefficients Φ).hadamard X + Matrix.diagonal
      (fun i => ∑ j, if i ≠ j then (transitionCoefficients Φ i j : ℂ) * X j j else 0) := by
  ext k l
  rw [matrixMap_entry_expansion]
  simp only [phase_matrixUnit_entries Φ h, Matrix.add_apply, Matrix.hadamard_apply,
    Matrix.diagonal_apply]
  by_cases hkl : k = l
  · subst l
    simp only [ite_true]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [schurCoefficients_diag]
    calc
      _ = ∑ a, ((if a = k then (transitionCoefficients Φ k k : ℂ) * X k k else 0) +
          (if k ≠ a then (transitionCoefficients Φ k a : ℂ) * X a a else 0)) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hak : a = k
        · subst a; simp [mul_comm]
        · simp [hak, Ne.symm hak, mul_comm]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  · simp [hkl, mul_ite, mul_comm, ite_and]

/-- The normal form is derived from actual covariance, complete positivity,
and trace preservation. -/
def normalFormOfPhaseCovariant (Φ : CPTPMap d d) (h : PhaseCovariant Φ) : NormalForm Φ where
  C := schurCoefficients Φ
  p := transitionCoefficients Φ
  C_psd := schurCoefficients_psd Φ
  p_nonneg := transitionCoefficients_nonneg Φ
  p_colsum := transitionCoefficients_colsum Φ
  C_diag := schurCoefficients_diag Φ
  action := phaseCovariant_action Φ h

/-- Entrywise action of a Schur-plus-classical normal form. -/
lemma NormalForm.action_apply (Φ : CPTPMap d d) (N : NormalForm Φ)
    (X : Matrix d d ℂ) (i j : d) :
    Φ.map X i j = N.C i j * X i j +
      if i = j then ∑ k, if i ≠ k then (N.p i k : ℂ) * X k k else 0 else 0 := by
  rw [N.action]
  simp [Matrix.hadamard_apply, Matrix.diagonal_apply]

/-- A channel in normal form commutes with every diagonal unitary. -/
theorem NormalForm.phaseCovariant (Φ : CPTPMap d d) (N : NormalForm Φ) :
    PhaseCovariant Φ := by
  intro z hz X
  ext i j
  have hzstar (k : d) : z k * star (z k) = 1 := by
    change z k * starRingEnd ℂ (z k) = 1
    rw [Complex.mul_conj]
    have : Complex.normSq (z k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz k]
      norm_num
    simp [this]
  have hentry (Y : Matrix d d ℂ) (a b : d) :
      (Matrix.diagonal z * Y * (Matrix.diagonal z)ᴴ) a b =
        z a * Y a b * star (z b) := by
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose, apply_ite]
  rw [N.action_apply, hentry]
  simp only [hentry, N.action_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [show z i * (N.C i i * X i i +
        ∑ k, if i ≠ k then (N.p i k : ℂ) * X k k else 0) * star (z i) =
        N.C i i * X i i + ∑ k, if i ≠ k then (N.p i k : ℂ) * X k k else 0 by
      calc
        _ = (z i * star (z i)) * (N.C i i * X i i +
            ∑ k, if i ≠ k then (N.p i k : ℂ) * X k k else 0) := by ring
        _ = _ := by rw [hzstar, one_mul]]
    congr 1
    · calc
        _ = (z i * star (z i)) * (N.C i i * X i i) := by ring
        _ = _ := by rw [hzstar, one_mul]
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs
      · calc
          _ = (z k * star (z k)) * ((N.p i k : ℂ) * X k k) := by ring
          _ = _ := by rw [hzstar, one_mul]
      · rfl
  · simp only [hij, ite_false, add_zero]
    ring

/-- Fixed-basis phase covariance is equivalent to the same-basis normal form. -/
theorem phaseCovariant_iff_normalForm (Φ : CPTPMap d d) :
    PhaseCovariant Φ ↔ Nonempty (NormalForm Φ) := by
  constructor
  · intro h
    exact ⟨normalFormOfPhaseCovariant Φ h⟩
  · rintro ⟨N⟩
    exact N.phaseCovariant Φ

/-- The angle-parametrized version of the fixed-basis normal-form theorem. -/
theorem phaseCovariantAngles_iff_normalForm (Φ : CPTPMap d d) :
    PhaseCovariantAngles Φ ↔ Nonempty (NormalForm Φ) := by
  rw [← phaseCovariant_iff_angles, phaseCovariant_iff_normalForm]

end SchurEntropy.PhaseCovariant
