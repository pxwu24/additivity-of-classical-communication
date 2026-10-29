import SchurEntropy.PhaseCovariant.Definitions

/-! # Matrix-unit support forced by fixed-basis phase covariance

Diagonal covariance distinguishes every off-diagonal matrix unit by its phase
character. Coordinate phases equal to `I` already suffice to separate these
characters; phases equal to `-1` alone would not distinguish their orientation.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Conjugation by a diagonal matrix scales each matrix unit by its character. -/
theorem diagonal_conjugate_matrixUnit (z : d → ℂ) (i j : d) :
    Matrix.diagonal z * Matrix.single i j 1 * (Matrix.diagonal z)ᴴ =
      (z i * star (z j)) • Matrix.single i j 1 := by
  ext k l
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp
    · simp [hjl]
  · simp [hik]

/-- Equivariance forces equality of the input and output phase characters on
every nonzero matrix coefficient. -/
theorem phase_matrixUnit_coefficient (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (z : d → ℂ) (hz : ∀ i, ‖z i‖ = 1) (i j k l : d) :
    (z i * star (z j)) * Φ.map (Matrix.single i j 1) k l =
      (z k * star (z l)) * Φ.map (Matrix.single i j 1) k l := by
  have hc := h z hz (Matrix.single i j 1)
  rw [diagonal_conjugate_matrixUnit, map_smul] at hc
  have he := congrArg (fun X : Matrix d d ℂ => X k l) hc
  simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply, mul_comm, mul_left_comm, mul_assoc] using he

private def coordinatePhase (t i : d) : ℂ := if i = t then Complex.I else 1

omit [Fintype d] in
private theorem coordinatePhase_norm (t : d) : ∀ i, ‖coordinatePhase t i‖ = 1 := by
  intro i
  unfold coordinatePhase
  split_ifs <;> simp

private theorem zero_of_distinct_coefficients {a b x : ℂ} (hab : a ≠ b)
    (h : a * x = b * x) : x = 0 := by
  by_contra hx
  exact hab (mul_right_cancel₀ hx h)

/-- A diagonal matrix unit has diagonal image under a phase-covariant map. -/
theorem phase_matrixUnit_diag_support (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (i k l : d) (hkl : k ≠ l) : Φ.map (Matrix.single i i 1) k l = 0 := by
  have hc := phase_matrixUnit_coefficient Φ h (coordinatePhase k)
    (coordinatePhase_norm k) i i k l
  by_cases hik : i = k
  · subst i
    simp [coordinatePhase, Ne.symm hkl] at hc
    exact zero_of_distinct_coefficients (a := 1) (b := Complex.I)
      (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)
  · simp [coordinatePhase, hik, Ne.symm hkl] at hc
    exact zero_of_distinct_coefficients (a := 1) (b := Complex.I)
      (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)

/-- An off-diagonal matrix unit can only have support at that same entry. -/
theorem phase_matrixUnit_offdiag_support (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (i j k l : d) (hij : i ≠ j) (hkl : k ≠ i ∨ l ≠ j) :
    Φ.map (Matrix.single i j 1) k l = 0 := by
  by_cases hki : k = i
  · subst k
    have hlj : l ≠ j := hkl.resolve_left (by simp)
    by_cases hli : l = i
    · subst l
      have hc := phase_matrixUnit_coefficient Φ h (coordinatePhase i)
        (coordinatePhase_norm i) i j i i
      simp [coordinatePhase, Ne.symm hij] at hc
      exact zero_of_distinct_coefficients (a := Complex.I) (b := 1)
        (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)
    · have hc := phase_matrixUnit_coefficient Φ h (coordinatePhase j)
        (coordinatePhase_norm j) i j i l
      simp [coordinatePhase, hij, hlj] at hc
      exact zero_of_distinct_coefficients (a := -Complex.I) (b := 1)
        (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)
  · have hc := phase_matrixUnit_coefficient Φ h (coordinatePhase i)
      (coordinatePhase_norm i) i j k l
    by_cases hli : l = i
    · subst l
      simp [coordinatePhase, Ne.symm hij, hki] at hc
      exact zero_of_distinct_coefficients (a := Complex.I) (b := -Complex.I)
        (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)
    · simp [coordinatePhase, Ne.symm hij, hki, hli] at hc
      exact zero_of_distinct_coefficients (a := Complex.I) (b := 1)
        (by intro he; have him := congrArg Complex.im he; norm_num at him) (by simpa using hc)

/-- The full support restriction implied by fixed-basis phase covariance. -/
theorem phase_matrixUnit_support (Φ : CPTPMap d d) (h : PhaseCovariant Φ)
    (i j k l : d) (hs : if i = j then k ≠ l else (k ≠ i ∨ l ≠ j)) :
    Φ.map (Matrix.single i j 1) k l = 0 := by
  by_cases hij : i = j
  · subst j
    exact phase_matrixUnit_diag_support Φ h i k l (by simpa using hs)
  · exact phase_matrixUnit_offdiag_support Φ h i j k l hij (by simpa [hij] using hs)

end SchurEntropy.PhaseCovariant
