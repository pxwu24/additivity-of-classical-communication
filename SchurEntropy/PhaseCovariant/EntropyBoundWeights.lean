import SchurEntropy.PhaseCovariant.EntropyBoundAlgebra
import SchurEntropy.PhaseCovariant.ComparisonState
import SchurEntropy.PhaseCovariant.NoiseEntropy

/-! The noise entropy terms collapse using column stochasticity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix QubitAdditivity
open scoped BigOperators Matrix ComplexOrder
namespace SchurEntropy.PhaseCovariant

variable {d f g : Type*} [Fintype d] [DecidableEq d]
  [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]

namespace NormalForm
variable {Φ : CPTPMap d d} (N : NormalForm Φ)

theorem noiseBlock_weights [Nonempty f] (Ω : CPTPMap f g)
    (ψ : d × f → ℂ) (i : d) :
    N.noiseBlock Ω ψ i = ∑ j, (if i ≠ j then N.p i j * branchMass ψ j else 0) •
      (Ω (vecState (inputBranch ψ j))).m := by
  unfold noiseBlock
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [partnerBlocks_diagonal, smul_smul]
  · rw [zero_smul]

omit [DecidableEq g] in
theorem noiseBlock_trace (Ω : CPTPMap f g) (ψ : d × f → ℂ) (i : d) :
    (Matrix.trace (N.noiseBlock Ω ψ i)).re = N.noiseWeights (branchMass ψ) i := by
  simp only [noiseBlock, Matrix.trace_sum, Complex.re_sum, noiseWeights]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [Matrix.trace_smul, Complex.smul_re, partnerBlocks_trace]
    rfl
  · simp

theorem noiseBlock_entropy_ge [Nonempty f] (Ω : CPTPMap f g)
    (ψ : d × f → ℂ) (i : d) :
    ∑ j, (if i ≠ j then N.p i j * branchMass ψ j else 0) *
      OpenAIEntropy.entropy (Ω (vecState (inputBranch ψ j))).m ≤
    OpenAIEntropy.entropy (N.noiseBlock Ω ψ i) -
      Real.negMulLog (N.noiseWeights (branchMass ψ) i) := by
  rw [N.noiseBlock_weights]
  apply entropy_mixture_sub_ge
  intro j
  split_ifs
  · exact mul_nonneg (N.p_nonneg i j) (branchMass_nonneg ψ j)
  · rfl

theorem diagonal_entropy_eq [Nonempty f] (Ω : CPTPMap f g)
    (ψ : d × f → ℂ) (i : d) :
    OpenAIEntropy.entropy ((N.C i i) • ((partnerBlocks Ω ψ).submatrix
      (fun x => (i,x)) (fun x => (i,x)))) -
      Real.negMulLog ((N.C i i).re * branchMass ψ i) =
    N.p i i * branchMass ψ i * OpenAIEntropy.entropy (Ω (vecState (inputBranch ψ i))).m := by
  rw [N.C_diag, Complex.ofReal_re, partnerBlocks_diagonal]
  have hsmul : (N.p i i : ℂ) • (branchMass ψ i • (Ω (vecState (inputBranch ψ i))).m) =
      (N.p i i * branchMass ψ i) • (Ω (vecState (inputBranch ψ i))).m := by
    ext x y
    simp [Complex.real_smul, mul_assoc]
  rw [hsmul, entropy_smul_state_sub]

theorem weighted_entropy_column_sum (r s : d → ℝ) :
    (∑ i, N.p i i * r i * s i) +
      (∑ i, ∑ j, (if i ≠ j then N.p i j * r j else 0) * s j) =
      ∑ j, r j * s j := by
  have hd : (∑ i, N.p i i * r i * s i) =
      ∑ j, ∑ i, if i = j then N.p i j * r j * s j else 0 := by simp
  rw [hd, Finset.sum_comm (f := fun i j =>
    (if i ≠ j then N.p i j * r j else 0) * s j), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  have he : (∑ i, ((if i = j then N.p i j * r j * s j else 0) +
      (if i ≠ j then N.p i j * r j else 0) * s j)) =
      ∑ i, N.p i j * r j * s j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i = j <;> simp [h]
  rw [he, ← Finset.sum_mul, ← Finset.sum_mul, N.p_colsum, one_mul]

theorem internal_entropy_ge [Nonempty f] (Ω : CPTPMap f g) (ψ : d × f → ℂ) :
    ∑ j, branchMass ψ j * OpenAIEntropy.entropy (Ω (vecState (inputBranch ψ j))).m ≤
      (∑ i, OpenAIEntropy.entropy ((N.C i i) • ((partnerBlocks Ω ψ).submatrix
        (fun x => (i,x)) (fun x => (i,x))))) -
      (∑ i, Real.negMulLog ((N.C i i).re * branchMass ψ i)) +
      (∑ i, OpenAIEntropy.entropy (N.noiseBlock Ω ψ i)) -
      (∑ i, Real.negMulLog (N.noiseWeights (branchMass ψ) i)) := by
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun i _ => N.noiseBlock_entropy_ge Ω ψ i)
  have hd := congrArg (fun h : d → ℝ => ∑ i, h i)
    (funext (N.diagonal_entropy_eq Ω ψ))
  simp only [Finset.sum_sub_distrib] at hn hd
  have he := N.weighted_entropy_column_sum (branchMass ψ)
    (fun j => OpenAIEntropy.entropy (Ω (vecState (inputBranch ψ j))).m)
  linarith

end NormalForm
end SchurEntropy.PhaseCovariant
