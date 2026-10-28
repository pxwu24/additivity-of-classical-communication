import QubitAdditivity.BetaPowers
import QuantumInfo.States.Mixed.MState

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace SchurEntropy.Capacity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The natural-log output-center pairing. `Real.log 0 = 0` gives the
spectral logarithm extended by zero on the kernel; support inclusion is a
separate theorem whenever this is used as a relative-entropy expression. -/
def logPairing (σ ρ : MState d) : ℝ :=
  (ρ.m * QubitAdditivity.BetaPowers.logarithm σ.m).trace.re

/-- Matrix-linear form underlying the output-center pairing. -/
def logPairingMatrix (σ : MState d) : Matrix d d ℂ →ₗ[ℝ] ℝ where
  toFun X := (X * QubitAdditivity.BetaPowers.logarithm σ.m).trace.re
  map_add' X Y := by simp [Matrix.add_mul]
  map_smul' t X := by simp

@[simp] theorem logPairingMatrix_apply (σ ρ : MState d) :
    logPairingMatrix σ ρ.m = logPairing σ ρ := rfl

end SchurEntropy.Capacity
