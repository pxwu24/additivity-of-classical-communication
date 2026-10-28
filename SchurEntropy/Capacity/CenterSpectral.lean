import SchurEntropy.Capacity.ScalarLogLimit
import QubitAdditivity.BetaLogKM
import QuantumInfo.ForMathlib.HermitianMat.Proj

/-!
# Spectral regularization of the center logarithm

The spectral basis is fixed at the unregularized matrix. Consequently the
regularized trace pairing is a finite sum of nonnegative weights times
`log (eigenvalue + t)`. A finite lower bound removes every kernel weight.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 20000
open Matrix Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

namespace SchurEntropy.Capacity
open QubitAdditivity QubitAdditivity.BetaPowers QubitAdditivity.BetaLogKM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_coordinates {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (X : Matrix ι ι ℂ) : (coordinates hA X).trace = X.trace := by
  rw [coordinates, Unitary.conjStarAlgAut_symm_apply, Matrix.trace_mul_cycle]
  simp

theorem coordinates_posSemidef {A R : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hR : R.PosSemidef) : (coordinates hA R).PosSemidef := by
  simpa only [coordinates, Unitary.conjStarAlgAut_symm_apply,
    Matrix.star_eq_conjTranspose] using
    hR.conjTranspose_mul_mul_same (hA.eigenvectorUnitary : Matrix ι ι ℂ)

theorem trace_mul_cfc_eq_weighted_sum (A R : HermitianMat ι ℂ) (f : ℝ → ℝ) :
    (R.mat * cfc f A.mat).trace.re =
      ∑ i, (coordinates A.H R.mat i i).re * f (A.H.eigenvalues i) := by
  have hc : coordinates A.H (cfc f A.mat) =
      Matrix.diagonal (fun i => (f (A.H.eigenvalues i) : ℂ)) := by
    convert! coordinates_cfc A.H f using 1
  rw [← trace_coordinates A.H (R.mat * cfc f A.mat), coordinates_mul, hc]
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]

theorem logarithm_shift_cfc (A : HermitianMat ι ℂ) (t : ℝ) :
    logarithm (A + t • 1).mat = cfc (fun x : ℝ => Real.log (x + t)) A.mat := by
  have hshift : A.cfc (fun x : ℝ => x + t) = A + t • 1 := by
    convert! HermitianMat.cfc_add_apply A id (fun _ => t) using 1
    simp
  have he := congrArg HermitianMat.mat
    (HermitianMat.cfc_comp_apply A (fun x : ℝ => x + t) Real.log)
  rw [hshift] at he
  exact he.symm

theorem trace_log_shift_eq_weighted_sum (A R : HermitianMat ι ℂ) (t : ℝ) :
    (R.mat * logarithm (A + t • 1).mat).trace.re =
      ∑ i, (coordinates A.H R.mat i i).re * Real.log (A.H.eigenvalues i + t) := by
  rw [logarithm_shift_cfc]
  exact trace_mul_cfc_eq_weighted_sum A R _

theorem spectral_weight_zero_of_log_shift_bddBelow (A R : HermitianMat ι ℂ)
    (hA : A.mat.PosSemidef) (hR : R.mat.PosSemidef)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0,
      B ≤ (R.mat * logarithm (A + t • 1).mat).trace.re)
    (i : ι) (hi : A.H.eigenvalues i = 0) :
    (coordinates A.H R.mat i i).re = 0 := by
  have hw (j : ι) : 0 ≤ (coordinates A.H R.mat j j).re :=
    (Complex.nonneg_iff.mp (coordinates_posSemidef A.H hR).diag_nonneg).1
  apply weight_zero_of_log_shift_bddBelow
    (fun j => (coordinates A.H R.mat j j).re) A.H.eigenvalues hw
    hA.eigenvalues_nonneg _ i hi
  simpa only [trace_log_shift_eq_weighted_sum] using hb

theorem trace_log_shift_tendsto_of_bddBelow (A R : HermitianMat ι ℂ)
    (hA : A.mat.PosSemidef) (hR : R.mat.PosSemidef)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0,
      B ≤ (R.mat * logarithm (A + t • 1).mat).trace.re) :
    Tendsto (fun t : ℝ => (R.mat * logarithm (A + t • 1).mat).trace.re)
      (𝓝[>] 0) (𝓝 (R.mat * logarithm A.mat).trace.re) := by
  have hw (j : ι) : 0 ≤ (coordinates A.H R.mat j j).re :=
    (Complex.nonneg_iff.mp (coordinates_posSemidef A.H hR).diag_nonneg).1
  have hb' : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0,
      B ≤ ∑ j, (coordinates A.H R.mat j j).re * Real.log (A.H.eigenvalues j + t) := by
    simpa only [trace_log_shift_eq_weighted_sum] using hb
  have ht := tendsto_sum_log_shift_of_bddBelow
    (fun j => (coordinates A.H R.mat j j).re) A.H.eigenvalues hw
    hA.eigenvalues_nonneg hb'
  have he0 : (R.mat * logarithm A.mat).trace.re =
      ∑ i, (coordinates A.H R.mat i i).re * Real.log (A.H.eigenvalues i) :=
    trace_mul_cfc_eq_weighted_sum A R Real.log
  rw [he0]
  have he : (fun t : ℝ => (R.mat * logarithm (A + t • 1).mat).trace.re) =
      (fun t : ℝ => ∑ i, (coordinates A.H R.mat i i).re *
        Real.log (A.H.eigenvalues i + t)) :=
    funext (trace_log_shift_eq_weighted_sum A R)
  rw [he]
  exact ht

/-- A finite lower bound for the regularized logarithmic pairing forces the
second positive matrix to live in the support of the first. -/
theorem support_le_of_log_shift_bddBelow (A R : HermitianMat ι ℂ)
    (hA : A.mat.PosSemidef) (hR : R.mat.PosSemidef)
    (hb : ∃ B : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0,
      B ≤ (R.mat * logarithm (A + t • 1).mat).trace.re) :
    R.support ≤ A.support := by
  have hs : inner ℝ R A.supportProj = R.trace := by
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.supportProj_eq_cfc]
    change (R.mat * cfc (fun x : ℝ => if x = 0 then 0 else 1) A.mat).trace.re = _
    rw [trace_mul_cfc_eq_weighted_sum]
    have h1 := trace_mul_cfc_eq_weighted_sum A R (fun _ => 1)
    have he : cfc (fun _ : ℝ => (1 : ℝ)) A.mat = 1 := by
      convert! congrArg HermitianMat.mat (HermitianMat.cfc_const A (1 : ℝ)) using 1
      simp
    rw [he, Matrix.mul_one] at h1
    rw [HermitianMat.trace_eq_re_trace]
    change _ = R.mat.trace.re
    rw [h1]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hz : A.H.eigenvalues i = 0
    · simp [hz, spectral_weight_zero_of_log_shift_bddBelow A R hA hR hb i hz]
    · simp [hz]
  have hk : inner ℝ R A.kerProj = 0 := by
    have he := congrArg (fun X : HermitianMat ι ℂ => inner ℝ R X)
      A.kerProj_add_supportProj
    rw [HermitianMat.inner_add_right, HermitianMat.inner_one, hs] at he
    linarith
  have hRn : 0 ≤ R := HermitianMat.zero_le_iff.mpr hR
  have hkn : 0 ≤ A.kerProj := HermitianMat.projector_nonneg A.ker
  simpa only [HermitianMat.kerProj_ker] using
    (HermitianMat.inner_zero_iff hRn hkn).mp hk

end SchurEntropy.Capacity
