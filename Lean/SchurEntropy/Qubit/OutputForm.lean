import QubitAdditivity.PureInput

/-! A single coherent Kraus branch and two families of commuting-output branches.
Adapted from QubitAdditivity.TwoExpectation and Partner at the pinned upstream
commit; generalized from qubit inputs to arbitrary finite input spaces. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix QubitAdditivity

namespace SchurEntropy.Qubit

/-- A qubit-output channel in the one-common-branch normal form: the common Kraus operator has rows
`a*` and `c*`; the operators with rows `b j*` reach only output 0, those with `d k*` only
output 1. -/
structure QubitOutputForm (D J K : Type*) [Fintype D] [Fintype J] [Fintype K] where
  a : D → ℂ
  c : D → ℂ
  b : J → D → ℂ
  d : K → D → ℂ

namespace QubitOutputForm

variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K] (N : QubitOutputForm D J K)

/-- The qubit output on an arbitrary input matrix. -/
def act (ρ : Matrix D D ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![bform ρ N.a N.a + ∑ j, bform ρ (N.b j) (N.b j), bform ρ N.a N.c;
     bform ρ N.c N.a, bform ρ N.c N.c + ∑ k, bform ρ (N.d k) (N.d k)]

/-- The four Frobenius masses of the output blocks at the input `ρ`. -/
def mx (ρ : Matrix D D ℂ) : ℝ := (bform ρ N.a N.a).re
def my (ρ : Matrix D D ℂ) : ℝ := ∑ j, (bform ρ (N.b j) (N.b j)).re
def mz (ρ : Matrix D D ℂ) : ℝ := (bform ρ N.c N.c).re
def mw (ρ : Matrix D D ℂ) : ℝ := ∑ k, (bform ρ (N.d k) (N.d k)).re

theorem act_isHermitian {σ : Matrix D D ℂ} (hσ : σ.IsHermitian) :
    (N.act σ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [act, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, star_add, star_sum, star_bform hσ]

theorem act_trace {σ : Matrix D D ℂ} (hσ : σ.IsHermitian) :
    (N.act σ).trace = ((N.mx σ + N.my σ + N.mz σ + N.mw σ : ℝ) : ℂ) := by
  have ha : bform σ N.a N.a = (N.mx σ : ℂ) := bform_self_eq_re hσ N.a
  have hc : bform σ N.c N.c = (N.mz σ : ℂ) := bform_self_eq_re hσ N.c
  have hb : ∑ j, bform σ (N.b j) (N.b j) = (N.my σ : ℂ) := sum_bform_self_eq_re hσ N.b
  have hd : ∑ k, bform σ (N.d k) (N.d k) = (N.mw σ : ℂ) := sum_bform_self_eq_re hσ N.d
  rw [act, Matrix.trace_fin_two_of, ha, hb, hc, hd]
  push_cast
  ring

theorem masses_nonneg {σ : Matrix D D ℂ} (hσ : σ.PosSemidef) :
    0 ≤ N.mx σ ∧ 0 ≤ N.my σ ∧ 0 ≤ N.mz σ ∧ 0 ≤ N.mw σ :=
  ⟨bform_self_re_nonneg hσ _, Finset.sum_nonneg fun _ _ => bform_self_re_nonneg hσ _,
    bform_self_re_nonneg hσ _, Finset.sum_nonneg fun _ _ => bform_self_re_nonneg hσ _⟩

/-- The rectangular matrix with rows `star u` and `star v`. -/
def rows (u v : D → ℂ) : Matrix (Fin 2) D ℂ :=
  fun i j => if i = 0 then star (u j) else star (v j)

@[simp] theorem rows_zero (u v : D → ℂ) (i : D) : rows u v 0 i = star (u i) := by
  simp [rows]

@[simp] theorem rows_one (u v : D → ℂ) (i : D) : rows u v 1 i = star (v i) := by
  simp [rows]

/-- The Kraus family: one coherent branch and two one-output families. -/
def kraus : Unit ⊕ (J ⊕ K) → Matrix (Fin 2) D ℂ
  | .inl _ => rows N.a N.c
  | .inr (.inl j) => rows (N.b j) 0
  | .inr (.inr k) => rows 0 (N.d k)

def Complete : Prop := ∑ f, (N.kraus f)ᴴ * N.kraus f = 1

theorem rows_conj (u v : D → ℂ) (ρ : Matrix D D ℂ) :
    rows u v * ρ * (rows u v)ᴴ = !![bform ρ u u, bform ρ u v; bform ρ v u, bform ρ v v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rows, Fin.isValue, reduceIte,
      star_star, bform, dotProduct, mulVec, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
  all_goals
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by simp [rows]; ring

theorem act_eq_of_kraus (ρ : Matrix D D ℂ) :
    MatrixMap.of_kraus N.kraus N.kraus ρ = N.act ρ := by
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_sum_type, Fintype.univ_punit, Finset.sum_singleton, kraus,
    rows_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [act, Matrix.sum_apply, bform, dotProduct, mulVec]

def toCPTP (h : N.Complete) : CPTPMap D (Fin 2) :=
  CPTPMap.of_kraus_CPTPMap N.kraus h

theorem toCPTP_m (h : N.Complete) (ρ : MState D) : (N.toCPTP h ρ).m = N.act ρ.m := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  exact N.act_eq_of_kraus ρ.m

end QubitOutputForm
end SchurEntropy.Qubit
