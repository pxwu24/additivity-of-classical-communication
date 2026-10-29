import SchurEntropy.Qubit.OutputForm
import QubitAdditivity.NormalChannel

/-!
# The manuscript's one-Kraus-plus-diagonal representation

This bridge retains the two positive effect operators explicitly. Their finite
outer-product decompositions provide the one-output Kraus families used by the
entropic argument.
The row Gram identities adapt the pinned `QubitAdditivity.NormalChannel`
proofs to arbitrary input dimension; see `third_party/NOTICE`.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixMap
open Matrix QubitAdditivity

namespace SchurEntropy.Qubit

variable {D J K : Type*} [Fintype D] [DecidableEq D] [Fintype J] [Fintype K]

/-- One coherent Kraus operator, followed by two commuting-output operations. -/
def singleCoherentAction (a c : D → ℂ) (E₀ E₁ X : Matrix D D ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  QubitOutputForm.rows a c * X * (QubitOutputForm.rows a c)ᴴ +
    Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace)

namespace QubitOutputForm

theorem rows_adjoint_rows (a c : D → ℂ) :
    (rows a c)ᴴ * rows a c = vecMulVec a (star a) + vecMulVec c (star c) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]

theorem kraus_sum (N : QubitOutputForm D J K) :
    (∑ j, (N.kraus j)ᴴ * N.kraus j) =
      vecMulVec N.a (star N.a) + vecMulVec N.c (star N.c) +
      (∑ j, vecMulVec (N.b j) (star (N.b j))) +
      ∑ k, vecMulVec (N.d k) (star (N.d k)) := by
  simp only [Fintype.sum_sum_type, Fintype.univ_punit, Finset.sum_singleton,
    kraus, rows_adjoint_rows, star_zero, Matrix.vecMulVec_zero,
    Matrix.zero_vecMulVec, add_zero, zero_add]
  abel

theorem act_eq_singleCoherentAction (N : QubitOutputForm D J K)
    (E₀ E₁ : Matrix D D ℂ)
    (h₀ : (∑ j, vecMulVec (N.b j) (star (N.b j))) = E₀)
    (h₁ : (∑ k, vecMulVec (N.d k) (star (N.d k))) = E₁)
    (X : Matrix D D ℂ) :
    N.act X = singleCoherentAction N.a N.c E₀ E₁ X := by
  have hb : (∑ j, bform X (N.b j) (N.b j)) = (E₀ * X).trace := by
    simp_rw [NormalChannel.bform_trace_outer]
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, h₀, Matrix.trace_mul_comm]
  have hd : (∑ k, bform X (N.d k) (N.d k)) = (E₁ * X).trace := by
    simp_rw [NormalChannel.bform_trace_outer]
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, h₁, Matrix.trace_mul_comm]
  rw [singleCoherentAction, rows_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [act, hb, hd]

end QubitOutputForm

/-- The positive-effect representation gives a complete concrete Kraus form. -/
theorem exists_outputForm_of_effects (a c : D → ℂ) (E₀ E₁ : Matrix D D ℂ)
    (h₀ : E₀.PosSemidef) (h₁ : E₁.PosSemidef)
    (hcomplete : vecMulVec a (star a) + vecMulVec c (star c) + E₀ + E₁ = 1) :
    ∃ N : QubitOutputForm D D D, ∃ hN : N.Complete,
      ∀ X, N.act X = singleCoherentAction a c E₀ E₁ X := by
  obtain ⟨b, hb⟩ := NormalKraus.exists_outer_decomposition h₀
  obtain ⟨d, hd⟩ := NormalKraus.exists_outer_decomposition h₁
  let N : QubitOutputForm D D D := ⟨a, c, b, d⟩
  have hN : N.Complete := by
    rw [QubitOutputForm.Complete, QubitOutputForm.kraus_sum]
    change vecMulVec a (star a) + vecMulVec c (star c) +
      (∑ j, vecMulVec (b j) (star (b j))) + ∑ k, vecMulVec (d k) (star (d k)) = 1
    change (∑ j, vecMulVec (b j) (star (b j))) = E₀ at hb
    change (∑ k, vecMulVec (d k) (star (d k))) = E₁ at hd
    rw [hb, hd]
    exact hcomplete
  refine ⟨N, hN, ?_⟩
  intro X
  exact N.act_eq_singleCoherentAction E₀ E₁ hb hd X

end SchurEntropy.Qubit
