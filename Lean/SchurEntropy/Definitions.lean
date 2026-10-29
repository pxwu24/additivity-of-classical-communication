import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix entropy and the main statement interfaces

The entropy below is the spectral entropy of an actual complex matrix, in bits.
The three final `...Statement` declarations are proposition-valued interfaces
for the two analytic lemmas and the block entropy theorem. Their proofs are
provided by `optimizedConcavity`, `scalar_joint_convexity`, and
`block_entropy_inequality` in the corresponding result modules.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy

/-- All coordinates of a finite direct sum, retaining their block labels. -/
abbrev BlockIndex {m : ℕ} (n : Fin m → ℕ) := (i : Fin m) × Fin (n i)

/-- Complex matrices acting on a direct sum of the specified finite blocks. -/
abbrev BlockMatrix {m : ℕ} (n : Fin m → ℕ) :=
  Matrix (BlockIndex n) (BlockIndex n) ℂ

/-- Unnormalized von Neumann entropy in bits. For Hermitian `A`, this is the
sum of `-λ log₂ λ` over its eigenvalues. No trace normalization is performed. -/
def entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog A)).re / Real.log 2

/-- The functional-calculus definition is the usual eigenvalue-sum entropy. -/
theorem entropy_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = (∑ i, Real.negMulLog (hA.eigenvalues i)) / Real.log 2 := by
  unfold entropy
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp [Function.comp_def]

/-- Entrywise multiplication by a scalar matrix on the block labels. -/
def blockSchur {m : ℕ} {n : Fin m → ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) (H : BlockMatrix n) : BlockMatrix n :=
  (C.submatrix Sigma.fst Sigma.fst).hadamard H

/-- Pinching onto diagonal blocks. -/
def pinching {m : ℕ} (n : Fin m → ℕ) (J : BlockMatrix n) : BlockMatrix n :=
  blockSchur (1 : Matrix (Fin m) (Fin m) ℂ) J

/-- A matrix is block diagonal exactly when pinching fixes it. -/
def IsBlockDiagonal {m : ℕ} (n : Fin m → ℕ) (W : BlockMatrix n) : Prop :=
  pinching n W = W

/-- Real traces of the diagonal blocks. They are nonnegative for PSD matrices. -/
def blockTrace {m : ℕ} (n : Fin m → ℕ) (J : BlockMatrix n) : Fin m → ℝ :=
  fun i => ∑ a : Fin (n i), (J ⟨i, a⟩ ⟨i, a⟩).re

/-- The entropy deficit associated with the prescribed block decomposition. -/
def deficit {m : ℕ} (n : Fin m → ℕ) (J W : BlockMatrix n) : ℝ :=
  entropy (J + W) - entropy (pinching n J) - entropy W

/-- Real scalar weights as a complex diagonal matrix. -/
def scalarDiagonal {m : ℕ} (y : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal (fun i => (y i : ℂ))

/-- The matrix `D_r^(1/2) C D_r^(1/2)`. -/
def scalarSkeleton {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) (r : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  scalarDiagonal (fun i => Real.sqrt (r i)) * C *
    scalarDiagonal (fun i => Real.sqrt (r i))

/-- Scalar-block entropy deficit, where pinching keeps only the diagonal. -/
def scalarDeficit {m : ℕ} (A W : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  entropy (A + W) - entropy (Matrix.diagonal A.diag) - entropy W

/-- The scalar function in the joint convexity lemma. -/
def scalarFunction {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ)
    (r y : Fin m → ℝ) : ℝ :=
  scalarDeficit (scalarSkeleton C r) (scalarDiagonal y)

/-- A multiplier that is constant on each block. -/
def blockMultiplier {m : ℕ} (n : Fin m → ℕ) (μ : Fin m → ℝ) : BlockMatrix n :=
  Matrix.diagonal (fun a : BlockIndex n => (μ a.1 : ℂ))

/-- The real scalar trace pairing. -/
def dot {m : ℕ} (μ y : Fin m → ℝ) : ℝ := ∑ i, μ i * y i

/-- The objective minimized in the optimized concavity lemma. -/
def dualCost {m : ℕ} (n : Fin m → ℕ) (μ : Fin m → ℝ)
    (J W : BlockMatrix n) : ℝ :=
  deficit n J W - (Matrix.trace (blockMultiplier n μ * W)).re

/-- The feasible noise matrices. -/
def admissibleNoise {m : ℕ} (n : Fin m → ℕ) : Set (BlockMatrix n) :=
  {W | W.PosSemidef ∧ IsBlockDiagonal n W}

/-- The infimum value. Attainment and concavity are separate analytic goals. -/
def optimizedDeficit {m : ℕ} (n : Fin m → ℕ) (μ : Fin m → ℝ)
    (J : BlockMatrix n) : ℝ :=
  sInf ((dualCost n μ J) '' admissibleNoise n)

@[simp] theorem blockSchur_apply {m : ℕ} {n : Fin m → ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) (H : BlockMatrix n)
    (a b : BlockIndex n) : blockSchur C H a b = C a.1 b.1 * H a b := rfl

@[simp] theorem pinching_apply {m : ℕ} (n : Fin m → ℕ)
    (J : BlockMatrix n) (a b : BlockIndex n) :
    pinching n J a b = if a.1 = b.1 then J a b else 0 := by
  simp [pinching, Matrix.one_apply]

theorem blockSchur_posSemidef {m : ℕ} {n : Fin m → ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} {H : BlockMatrix n}
    (hC : C.PosSemidef) (hH : H.PosSemidef) :
    (blockSchur C H).PosSemidef :=
  (hC.submatrix Sigma.fst).hadamard hH

@[simp] theorem blockSchur_add {m : ℕ} {n : Fin m → ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) (H K : BlockMatrix n) :
    blockSchur C (H + K) = blockSchur C H + blockSchur C K := by
  ext a b
  simp [mul_add]

@[simp] theorem blockSchur_smul {m : ℕ} {n : Fin m → ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) (t : ℝ) (H : BlockMatrix n) :
    blockSchur C (t • H) = t • blockSchur C H := by
  ext a b
  simp [mul_left_comm]

@[simp] theorem scalarDiagonal_conjTranspose {m : ℕ} (r : Fin m → ℝ) :
    (scalarDiagonal r).conjTranspose = scalarDiagonal r := by
  simp [scalarDiagonal, Matrix.diagonal_conjTranspose]

theorem scalarSkeleton_posSemidef {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : C.PosSemidef) (r : Fin m → ℝ) :
    (scalarSkeleton C r).PosSemidef := by
  simpa [scalarSkeleton] using
    hC.conjTranspose_mul_mul_same (scalarDiagonal (fun i => Real.sqrt (r i)))

theorem pinching_posSemidef {m : ℕ} (n : Fin m → ℕ)
    {J : BlockMatrix n} (hJ : J.PosSemidef) : (pinching n J).PosSemidef :=
  blockSchur_posSemidef Matrix.PosSemidef.one hJ

@[simp] theorem pinching_idempotent {m : ℕ} (n : Fin m → ℕ)
    (J : BlockMatrix n) : pinching n (pinching n J) = pinching n J := by
  ext a b
  simp only [pinching_apply]
  split <;> simp_all

@[simp] theorem trace_pinching {m : ℕ} (n : Fin m → ℕ)
    (J : BlockMatrix n) : Matrix.trace (pinching n J) = Matrix.trace J := by
  simp [Matrix.trace, Matrix.diag_apply]

@[simp] theorem blockTrace_pinching {m : ℕ} (n : Fin m → ℕ)
    (J : BlockMatrix n) : blockTrace n (pinching n J) = blockTrace n J := by
  funext i
  simp [blockTrace]

theorem isBlockDiagonal_iff {m : ℕ} (n : Fin m → ℕ) (W : BlockMatrix n) :
    IsBlockDiagonal n W ↔ ∀ a b : BlockIndex n, a.1 ≠ b.1 → W a b = 0 := by
  constructor
  · intro h a b hab
    have heq := congrArg (fun M : BlockMatrix n => M a b) h
    simpa [pinching_apply, hab] using heq.symm
  · intro h
    ext a b
    by_cases hab : a.1 = b.1
    · simp [pinching_apply, hab]
    · simp [pinching_apply, hab, h a b hab]

theorem zero_mem_admissibleNoise {m : ℕ} (n : Fin m → ℕ) :
    (0 : BlockMatrix n) ∈ admissibleNoise n := by
  refine ⟨Matrix.PosSemidef.zero, ?_⟩
  apply (isBlockDiagonal_iff n 0).2
  simp

theorem admissibleNoise_nonempty {m : ℕ} (n : Fin m → ℕ) :
    (admissibleNoise n).Nonempty := ⟨0, zero_mem_admissibleNoise n⟩

theorem trace_eq_sum_blockTrace {m : ℕ} (n : Fin m → ℕ) (J : BlockMatrix n) :
    (Matrix.trace J).re = ∑ i, blockTrace n J i := by
  simp [Matrix.trace, Matrix.diag_apply, blockTrace, Fintype.sum_sigma]

theorem blockTrace_nonneg {m : ℕ} (n : Fin m → ℕ)
    {J : BlockMatrix n} (hJ : J.PosSemidef) (i : Fin m) : 0 ≤ blockTrace n J i := by
  apply Finset.sum_nonneg
  intro a ha
  exact (Complex.nonneg_iff.mp hJ.diag_nonneg).1

@[simp] theorem blockTrace_add {m : ℕ} (n : Fin m → ℕ)
    (J K : BlockMatrix n) : blockTrace n (J + K) = blockTrace n J + blockTrace n K := by
  funext i
  simp [blockTrace, Finset.sum_add_distrib]

@[simp] theorem blockTrace_smul {m : ℕ} (n : Fin m → ℕ)
    (t : ℝ) (J : BlockMatrix n) : blockTrace n (t • J) = t • blockTrace n J := by
  funext i
  simp [blockTrace, Finset.mul_sum]

theorem trace_blockMultiplier_mul {m : ℕ} (n : Fin m → ℕ)
    (μ : Fin m → ℝ) (W : BlockMatrix n) :
    (Matrix.trace (blockMultiplier n μ * W)).re = dot μ (blockTrace n W) := by
  simp [blockMultiplier, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
    Complex.mul_re, Fintype.sum_sigma, dot, blockTrace, Finset.mul_sum]

theorem dualCost_eq {m : ℕ} (n : Fin m → ℕ) (μ : Fin m → ℝ)
    (J W : BlockMatrix n) :
    dualCost n μ J W = deficit n J W - dot μ (blockTrace n W) := by
  rw [dualCost, trace_blockMultiplier_mul]

/-- Statement interface for attainment and optimized concavity, proved by
`optimizedConcavity` in `OptimizedBridge`. -/
def OptimizedConcavityStatement : Prop :=
  ∀ (m : ℕ) (n : Fin m → ℕ) (μ : Fin m → ℝ),
    0 < m → (∀ i, 0 < n i) → (∀ i, μ i < 0) →
      (∀ J : BlockMatrix n, J.PosSemidef →
        ∃ W ∈ admissibleNoise n,
          optimizedDeficit n μ J = dualCost n μ J W ∧
          ∀ Z ∈ admissibleNoise n, dualCost n μ J W ≤ dualCost n μ J Z) ∧
      ConcaveOn ℝ {J : BlockMatrix n | J.PosSemidef} (optimizedDeficit n μ)

/-- Statement interface for scalar joint convexity, proved by
`scalar_joint_convexity` in `ScalarConvexity`. -/
def ScalarConvexityStatement : Prop :=
  ∀ (m : ℕ) (C : Matrix (Fin m) (Fin m) ℂ), 0 < m → C.PosSemidef →
    ConvexOn ℝ {p : (Fin m → ℝ) × (Fin m → ℝ) |
      (∀ i, 0 ≤ p.1 i) ∧ (∀ i, 0 ≤ p.2 i)}
      (fun p => scalarFunction C p.1 p.2)

/-- Statement interface for the Schur-weighted block entropy inequality,
proved by `block_entropy_inequality` in `Results`. -/
def BlockEntropyStatement : Prop :=
  ∀ (m : ℕ) (n : Fin m → ℕ)
    (C : Matrix (Fin m) (Fin m) ℂ) (H W : BlockMatrix n),
    0 < m → (∀ i, 0 < n i) → C.PosSemidef → H.PosSemidef → W.PosSemidef →
    IsBlockDiagonal n W →
    scalarFunction C (blockTrace n H) (blockTrace n W) ≤ deficit n (blockSchur C H) W

end SchurEntropy
