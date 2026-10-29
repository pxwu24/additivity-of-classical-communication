import SchurEntropy.PhaseCovariant.Definitions
import QubitAdditivity.PureInput
import SchurEntropy.Definitions

/-! Positive-amplitude comparison states in the fixed covariance basis. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy.PhaseCovariant

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The nonnegative real amplitudes associated with a probability vector. -/
def sqrtVector (r : d → ℝ) : d → ℂ := fun i => (Real.sqrt (r i) : ℂ)

/-- The normalized ket with nonnegative real amplitudes. -/
def sqrtKet (r : d → ℝ) (hr : ∀ i, 0 ≤ r i) (hsum : ∑ i, r i = 1) : Ket d where
  vec := sqrtVector r
  normalized' := by
    simpa only [sqrtVector, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal,
      Real.mul_self_sqrt (hr _)] using hsum

/-- A pure-state matrix with prescribed diagonal probabilities. -/
def sqrtState (r : d → ℝ) (hr : ∀ i, 0 ≤ r i) (hsum : ∑ i, r i = 1) : MState d :=
  QubitAdditivity.stateOf (vecMulVec (sqrtVector r) (star (sqrtVector r))) ⟨
    Matrix.posSemidef_vecMulVec_self_star _, by
      simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, sqrtVector,
        Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hr _), ← Complex.ofReal_sum, hsum, Complex.ofReal_one]⟩

theorem sqrtState_eq_pure (r : d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) : sqrtState r hr hsum = MState.pure (sqrtKet r hr hsum) := by
  apply MState.ext_m
  rw [QubitAdditivity.pure_m]
  rfl

@[simp] theorem sqrtState_m (r : d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (i j : d) :
    (sqrtState r hr hsum).m i j = (Real.sqrt (r i) * Real.sqrt (r j) : ℝ) := by
  change Matrix.vecMulVec (sqrtVector r) (star (sqrtVector r)) i j = _
  simp [Matrix.vecMulVec_apply, sqrtVector]

@[simp] theorem sqrtState_diag (r : d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (i : d) :
    (sqrtState r hr hsum).m i i = (r i : ℂ) := by
  rw [sqrtState_m, Real.mul_self_sqrt (hr i)]

theorem state_diag_nonneg (ρ : MState d) (i : d) : 0 ≤ (ρ.m i i).re :=
  (Complex.nonneg_iff.mp (ρ.psd.diag_nonneg (i := i))).1

theorem state_diag_real (ρ : MState d) (i : d) : ((ρ.m i i).re : ℂ) = ρ.m i i := by
  apply Complex.ext
  · simp
  · simpa using (Complex.nonneg_iff.mp (ρ.psd.diag_nonneg (i := i))).2

theorem state_diag_sum (ρ : MState d) : ∑ i, (ρ.m i i).re = 1 := by
  have h := congrArg Complex.re ρ.tr'
  simpa [Matrix.trace, Matrix.diag] using h

/-- The state of `∑ i, √(ρᵢᵢ) |i⟩`; its basis is the channel's fixed basis. -/
def comparisonState (ρ : MState d) : MState d :=
  sqrtState (fun i => (ρ.m i i).re) (state_diag_nonneg ρ) (state_diag_sum ρ)

@[simp] theorem comparisonState_m (ρ : MState d) (i j : d) :
    (comparisonState ρ).m i j =
      (Real.sqrt (ρ.m i i).re * Real.sqrt (ρ.m j j).re : ℝ) :=
  sqrtState_m _ _ _ _ _

@[simp] theorem comparisonState_diag (ρ : MState d) (i : d) :
    (comparisonState ρ).m i i = ρ.m i i := by
  rw [comparisonState, sqrtState_diag, state_diag_real]

namespace NormalForm
variable {Φ : CPTPMap d d} (N : NormalForm Φ)

/-- Classical noise masses for a prescribed input diagonal. -/
def noiseWeights (r : d → ℝ) (i : d) : ℝ :=
  ∑ j, if i ≠ j then N.p i j * r j else 0

theorem noiseWeights_nonneg (r : d → ℝ) (hr : ∀ i, 0 ≤ r i) (i : d) :
    0 ≤ N.noiseWeights r i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact mul_nonneg (N.p_nonneg i j) (hr j)
  · rfl

include N in
/-- Only input diagonal entries affect output diagonal entries. -/
theorem output_diag_eq {ρ τ : MState d} (hdiag : ∀ i, ρ.m i i = τ.m i i) (i : d) :
    (Φ ρ).m i i = (Φ τ).m i i := by
  simp only [CPTPMap.mat_coe_eq_apply_mat, N.action, Matrix.add_apply,
    Matrix.hadamard_apply, Matrix.diagonal_apply_eq, hdiag]

include N in
/-- The comparison input has exactly the same output diagonal as the given state. -/
theorem comparisonState_output_diag (ρ : MState d) (i : d) :
    (Φ (comparisonState ρ)).m i i = (Φ ρ).m i i :=
  N.output_diag_eq (comparisonState_diag ρ) i

theorem sqrtState_output_entry (r : d → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) (i j : d) :
    (Φ (sqrtState r hr hsum)).m i j =
      N.C i j * (Real.sqrt (r i) : ℂ) * (Real.sqrt (r j) : ℂ) +
      if i = j then (N.noiseWeights r i : ℂ) else 0 := by
  rw [CPTPMap.mat_coe_eq_apply_mat, N.action]
  simp only [Matrix.add_apply, Matrix.hadamard_apply, sqrtState_m,
    Complex.ofReal_mul, Matrix.diagonal_apply]
  congr 1
  · ring
  · split_ifs with hij
    · simp only [noiseWeights, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hr _)]
    · rfl

end NormalForm

/-- The comparison output is precisely the scalar matrix in the block inequality. -/
theorem NormalForm.sqrtState_output_m {m : ℕ} {Φ : CPTPMap (Fin m) (Fin m)}
    (N : NormalForm Φ) (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hsum : ∑ i, r i = 1) :
    (Φ (sqrtState r hr hsum)).m = scalarSkeleton N.C r + scalarDiagonal (N.noiseWeights r) := by
  ext i j
  rw [N.sqrtState_output_entry]
  simp only [scalarSkeleton, scalarDiagonal, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.diagonal_apply]
  ring

end SchurEntropy.PhaseCovariant
