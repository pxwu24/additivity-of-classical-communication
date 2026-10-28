import SchurEntropy.Capacity.RegularizedEntropy
import SchurEntropy.Capacity.CenterSpectral
import SchurEntropy.Capacity.LogPairing

/-! State-level regularization at a possibly singular output center. A lower
bound on the regularized pairing forces every spectral weight on its kernel
to vanish, and gives convergence to the finite spectral logarithm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Matrix Filter Set
open scoped ComplexOrder MatrixOrder Topology

namespace SchurEntropy.Capacity
open QubitAdditivity QubitAdditivity.BetaEntropy QubitAdditivity.BetaPowers

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Pairing with the logarithm of the strictly positive regularized center. -/
def regularizedLogPairing (σ ρ : MState d) (t : ℝ) : ℝ :=
  (ρ.m * logarithm (σ.m + t • (1 : Matrix d d ℂ))).trace.re

/-- Entropy-increment upper bound along an arbitrary state direction. -/
theorem psi_state_increment_le_regularized (σ ρ : MState d) {t : ℝ} (ht : 0 < t) :
    psi (σ.M + t • ρ.M) - psi σ.M ≤ t * (regularizedLogPairing σ ρ t + 1) := by
  simpa [regularizedLogPairing, MState.tr'] using
    psi_increment_le_regularized_log σ.psd ρ.psd ρ.le_one ht

/-- Boundedness at zero rules out positive state weight in any zero
eigenspace of the center. -/
theorem kernel_weight_zero_of_regularized_bddBelow (σ ρ : MState d)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, B ≤ regularizedLogPairing σ ρ t)
    (i : d) (hi : σ.M.H.eigenvalues i = 0) :
    (BetaLogKM.coordinates σ.M.H ρ.m i i).re = 0 := by
  exact spectral_weight_zero_of_log_shift_bddBelow σ.M ρ.M σ.psd ρ.psd hb i hi

/-- The regularized pairing converges to the center pairing whenever it has
a finite lower bound; no strict positivity of the center is required. -/
theorem regularizedLogPairing_tendsto_of_bddBelow (σ ρ : MState d)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, B ≤ regularizedLogPairing σ ρ t) :
    Tendsto (regularizedLogPairing σ ρ) (𝓝[>] 0) (𝓝 (logPairing σ ρ)) := by
  exact trace_log_shift_tendsto_of_bddBelow σ.M ρ.M σ.psd ρ.psd hb

/-- The finite lower bound also proves actual inclusion of state supports. -/
theorem support_le_of_regularized_bddBelow (σ ρ : MState d)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0, B ≤ regularizedLogPairing σ ρ t) :
    ρ.M.support ≤ σ.M.support := by
  exact support_le_of_log_shift_bddBelow σ.M ρ.M σ.psd ρ.psd hb

end SchurEntropy.Capacity
