import SchurEntropy.Qubit.OutputForm

/-! Generic-input channel and marginal algebra. Adapted from the pinned
QubitAdditivity.Partner, with qubit input sums replaced by arbitrary finite sums. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix QubitAdditivity
namespace SchurEntropy.Qubit

/-- Contraction of the first subsystem against a vector. -/
def branch {D dB : Type*} [Fintype D] (u : D → ℂ) (ψ : D × dB → ℂ) : dB → ℂ :=
  fun j => ∑ i, star (u i) * ψ (i, j)

namespace QubitOutputForm

variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K] (N : QubitOutputForm D J K)
variable {dB eB κ : Type*} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]
variable [Fintype κ]

/-- The four output blocks of TC4 for the input `ψ`. -/
def blockA (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) : Matrix eB (Unit × κ) ℂ :=
  branchBlock W fun _ : Unit => branch N.a ψ

def blockB (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) : Matrix eB (J × κ) ℂ :=
  branchBlock W fun j => branch (N.b j) ψ

def blockC (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) : Matrix eB (Unit × κ) ℂ :=
  branchBlock W fun _ : Unit => branch N.c ψ

def blockD (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) : Matrix eB (K × κ) ℂ :=
  branchBlock W fun k => branch (N.d k) ψ

/-- The joint Kraus family of the normal form and `W`. -/
def jointKraus (W : κ → Matrix eB dB ℂ) :
    (Unit ⊕ (J ⊕ K)) × κ → Matrix (Fin 2 × eB) (D × dB) ℂ :=
  fun x => N.kraus x.1 ⊗ₖ W x.2

/-- The four-block matrix of TC4 at the input `ψ`. -/
def tc4At (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) :
    Matrix (eB ⊕ eB) ((Unit × κ) ⊕ ((J × κ) ⊕ (K × κ))) ℂ :=
  tc4Matrix (N.blockA W ψ) (N.blockB W ψ) (N.blockC W ψ) (N.blockD W ψ)

/-- The joint column matrix is the four-block matrix of TC4, up to relabelling. -/
theorem jointColumns_eq (W : κ → Matrix eB dB ℂ) (ψ : D × dB → ℂ) :
    krausColumns (N.jointKraus W) ψ =
      (N.tc4At W ψ).submatrix (rowEquiv eB) (colEquiv J K κ) := by
  ext ⟨o, o'⟩ ⟨f, μ⟩
  fin_cases o <;> rcases f with ⟨⟩ | j | k <;>
    simp [krausColumns, jointKraus, tc4At, tc4Matrix, rowEquiv, colEquiv, blockA, blockB,
      blockC, blockD, branchBlock, branch, kraus, rows_zero, rows_one, mulVec, dotProduct,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum]
  all_goals
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem jointKraus_eq_kron (W : κ → Matrix eB dB ℂ) :
    MatrixMap.of_kraus N.kraus N.kraus ⊗ₖₘ MatrixMap.of_kraus W W =
      MatrixMap.of_kraus (N.jointKraus W) (N.jointKraus W) :=
  MatrixMap.kron_of_kraus N.kraus W

/-- The joint output of the normal form and a partner channel on a pure input is the Gram
matrix of the four-block matrix, up to relabelling the rows. -/
theorem joint_output_m (h : N.Complete) (Ω : CPTPMap dB eB) (W : κ → Matrix eB dB ℂ)
    (hW : Ω.map = MatrixMap.of_kraus W W) (ψ : Ket (D × dB)) :
    ((N.toCPTP h ⊗ᶜᵖ Ω) (MState.pure ψ)).m =
      (N.tc4At W ψ * (N.tc4At W ψ).conjTranspose).submatrix (rowEquiv eB) (rowEquiv eB) := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (MatrixMap.of_kraus N.kraus N.kraus ⊗ₖₘ Ω.map) (MState.pure ψ).m = _
  rw [hW, N.jointKraus_eq_kron, pure_m, of_kraus_vecMulVec, N.jointColumns_eq,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

end QubitOutputForm


section marginals
variable {D dB : Type*} [Fintype D] [DecidableEq D] [Fintype dB] [DecidableEq dB]

theorem traceRight_pure_m (ψ : Ket (D × dB)) :
    (MState.pure ψ).traceRight.m = Matrix.of fun i k => ∑ j, ψ (i, j) * star (ψ (k, j)) := by
  change (MState.pure ψ).m.traceRight = _
  rw [pure_m]
  ext i k
  simp [Matrix.traceRight, vecMulVec_apply]

theorem traceLeft_pure_m (ψ : Ket (D × dB)) :
    (MState.pure ψ).traceLeft.m = Matrix.of fun x y => ∑ i, ψ (i, x) * star (ψ (i, y)) := by
  change (MState.pure ψ).m.traceLeft = _
  rw [pure_m]
  ext x y
  simp [Matrix.traceLeft, vecMulVec_apply]

theorem vecMass_branch (ψ : Ket (D × dB)) (u : D → ℂ) :
    vecMass (branch u ψ) = (bform (MState.pure ψ).traceRight.m u u).re := by
  have h : bform (MState.pure ψ).traceRight.m u u =
      ∑ j, branch u ψ j * star (branch u ψ j) := by
    rw [traceRight_pure_m]
    simp only [bform, dotProduct, mulVec, Matrix.of_apply, branch, Pi.star_apply,
      star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, vecMass, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show star (branch u ψ j) = (starRingEnd ℂ) (branch u ψ j) from rfl, Complex.mul_conj,
    Complex.ofReal_re]

theorem sum_branch_outer {L : Type*} [Fintype L] (u : L → D → ℂ) (ψ : D × dB → ℂ)
    (x y : dB) :
    ∑ l, branch (u l) ψ x * star (branch (u l) ψ y) =
      ∑ i, ∑ k, ψ (i, x) * star (ψ (k, y)) * ∑ l, u l k * star (u l i) := by
  simp only [branch, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end marginals

namespace QubitOutputForm
variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K]
variable (N : QubitOutputForm D J K)

theorem complete_entry (h : N.Complete) (k i : D) :
    N.a k * star (N.a i) + N.c k * star (N.c i) + ∑ j, N.b j k * star (N.b j i) +
      ∑ l, N.d l k * star (N.d l i) = (1 : Matrix D D ℂ) k i := by
  have hk := congrFun (congrFun h k) i
  rw [← hk]
  simp only [Matrix.sum_apply, Fintype.sum_sum_type, Fintype.univ_punit, Finset.sum_singleton,
    kraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, rows_zero, rows_one,
    star_star, Pi.zero_apply, star_zero, zero_mul, add_zero, zero_add]
  ring

variable {dB : Type*} [Fintype dB] [DecidableEq dB]

theorem traceLeft_pure_eq (h : N.Complete) (ψ : Ket (D × dB)) :
    (MState.pure ψ).traceLeft.m =
      vecMulVec (branch N.a ψ) (star (branch N.a ψ)) +
        ∑ j, vecMulVec (branch (N.b j) ψ) (star (branch (N.b j) ψ)) +
        vecMulVec (branch N.c ψ) (star (branch N.c ψ)) +
        ∑ l, vecMulVec (branch (N.d l) ψ) (star (branch (N.d l) ψ)) := by
  rw [traceLeft_pure_m]
  ext x y
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
    Pi.star_apply]
  have ha := sum_branch_outer (fun _ : Unit => N.a) ψ x y
  have hc := sum_branch_outer (fun _ : Unit => N.c) ψ x y
  have hb := sum_branch_outer N.b ψ x y
  have hd := sum_branch_outer N.d ψ x y
  simp only [Fintype.univ_punit, Finset.sum_singleton] at ha hc
  rw [ha, hc, hb, hd]
  simp only [← Finset.sum_add_distrib]
  have he : ∀ i k, ψ (i, x) * star (ψ (k, y)) * (N.a k * star (N.a i)) +
      ψ (i, x) * star (ψ (k, y)) * ∑ j, N.b j k * star (N.b j i) +
      ψ (i, x) * star (ψ (k, y)) * (N.c k * star (N.c i)) +
      ψ (i, x) * star (ψ (k, y)) * ∑ l, N.d l k * star (N.d l i) =
      ψ (i, x) * star (ψ (k, y)) * (1 : Matrix D D ℂ) k i := by
    intro i k
    rw [← N.complete_entry h k i]
    ring
  simp_rw [he]
  simp [Matrix.one_apply]

end QubitOutputForm
end SchurEntropy.Qubit
