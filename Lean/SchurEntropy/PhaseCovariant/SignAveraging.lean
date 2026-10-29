import QubitAdditivity.BetaSignFrame
import QubitAdditivity.RotationInvariant
import QubitAdditivity.UpperBound

/-! Finite diagonal sign averaging realizes diagonal pinching exactly. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace SchurEntropy.PhaseCovariant
open QubitAdditivity QubitAdditivity.BetaSignFrame

@[reducible] local instance signAveragingMatrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The diagonal unitary associated with a choice of real signs. -/
def signUnitary (f : d → Bool) : Matrix.unitaryGroup d ℂ :=
  ⟨Matrix.diagonal (fun i => sign (f i)), by
    constructor <;> change _ = (1 : Matrix d d ℂ) <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Pi.star_apply, star_sign, sign_sq,
        Matrix.diagonal_one]⟩

@[simp] theorem signUnitary_val (f : d → Bool) :
    (signUnitary f : Matrix d d ℂ) = Matrix.diagonal (fun i => sign (f i)) := rfl

@[simp] theorem norm_sign (b : Bool) : ‖sign b‖ = 1 := by
  cases b <;> norm_num [sign]

/-- A finite orbit ensemble under all diagonal sign unitaries. -/
def signOrbit (ρ : MState d) : MEnsemble d (d → Bool) :=
  ⟨fun f => CPTPMap.ofUnitary (signUnitary f) ρ, ProbDistribution.uniform⟩

@[simp] theorem signOrbit_distr (ρ : MState d) (f : d → Bool) :
    ((signOrbit ρ).distr f : ℝ) = 1 / Fintype.card (d → Bool) := rfl

@[simp] theorem signOrbit_states (ρ : MState d) (f : d → Bool) :
    (signOrbit ρ).states f = CPTPMap.ofUnitary (signUnitary f) ρ := rfl

/-- Averaging the sign orbit deletes exactly the off-diagonal entries. -/
theorem signOrbit_mix (ρ : MState d) :
    (Ensemble.mix (signOrbit ρ)).m = Matrix.diagonal (fun i => ρ.m i i) := by
  rw [Ensemble.mix_of]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, signOrbit_distr, signOrbit_states,
    CPTPMap.mat_coe_eq_apply_mat]
  change (∑ f : d → Bool, (1 / (Fintype.card (d → Bool) : ℝ)) •
    (Matrix.diagonal (fun i => sign (f i)) * ρ.m *
      (Matrix.diagonal (fun i => sign (f i)))ᴴ) i j) = _
  simp only [Matrix.diagonal_conjTranspose, Pi.star_apply, star_sign, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Complex.real_smul]
  have he (f : d → Bool) :
      ((1 / (Fintype.card (d → Bool) : ℝ) : ℝ) : ℂ) *
      (sign (f i) * ρ.m i j * sign (f j)) =
      ((1 / (Fintype.card (d → Bool) : ℝ) : ℝ) : ℂ) * ρ.m i j *
      (sign (f i) * sign (f j)) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, sum_sign_mul]
  have hc : (Fintype.card (d → Bool) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Matrix.diagonal_apply_eq, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_natCast]
    field_simp
  · simp [hij]

/-- Entropy cannot decrease under finite sign averaging. -/
theorem entropy_signOrbit_mix (ρ : MState d) :
    Sᵥₙ ρ ≤ Sᵥₙ (Ensemble.mix (signOrbit ρ)) := by
  have h := entropy_mix_ge (signOrbit ρ)
  simp only [signOrbit_states, RotationInvariant.entropy_output_unitary] at h
  simpa only [← Finset.sum_mul, ProbDistribution.normalized, one_mul] using h

end SchurEntropy.PhaseCovariant
