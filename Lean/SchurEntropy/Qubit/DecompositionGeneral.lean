import SchurEntropy.Qubit.DecompositionAlgebra
import SchurEntropy.Qubit.Representation
import SchurEntropy.Qubit.PSDFactor
import SchurEntropy.Qubit.RankPadding

/-!
# The finite-rank decomposition of every qubit-output channel

The output rotation makes the dual cross block singular. A positive block
factorization extracts a coherent remainder with rank-many Kraus operators;
the positive diagonal residuals form the two commuting-output effects.
The unitary Kraus identities adapt the pinned `QubitAdditivity.NormalChannel`
proofs to arbitrary input dimension; see `third_party/NOTICE`.
-/

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix QubitAdditivity
open scoped Matrix BigOperators ComplexOrder MatrixOrder MatrixMap

namespace SchurEntropy.Qubit

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

def rowGramAction (P Q B X : Matrix n n ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(X * P).trace, (X * B).trace; (X * Bᴴ).trace, (X * Q).trace]

theorem rows_family_gram_action (p q : k → n → ℂ) (X : Matrix n n ℂ) :
    MatrixMap.of_kraus (fun j => QubitOutputForm.rows (p j) (q j))
      (fun j => QubitOutputForm.rows (p j) (q j)) X =
      rowGramAction (rowMass p) (rowMass q) (rowCross p q) X := by
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk, QubitOutputForm.rows_conj]
  simp_rw [NormalChannel.bform_trace_outer]
  rw [rowGramAction, rowCross_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowMass, rowCross, Matrix.mul_sum, Matrix.trace_sum, Matrix.sum_apply]

theorem rows_sum_gram_action (p q : k → n → ℂ) (X : Matrix n n ℂ) :
    (∑ j, QubitOutputForm.rows (p j) (q j) * X * (QubitOutputForm.rows (p j) (q j))ᴴ) =
      rowGramAction (rowMass p) (rowMass q) (rowCross p q) X := by
  simpa only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk] using rows_family_gram_action p q X

theorem rows_family_gram_complete (p q : k → n → ℂ) :
    (∑ j, (QubitOutputForm.rows (p j) (q j))ᴴ * QubitOutputForm.rows (p j) (q j)) =
      rowMass p + rowMass q := by
  simp only [QubitOutputForm.rows_adjoint_rows, Finset.sum_add_distrib, rowMass]

theorem rowGramAction_add_effects (p q : k → n → ℂ)
    (E₀ E₁ X : Matrix n n ℂ) :
    rowGramAction (rowMass p + E₀) (rowMass q + E₁) (rowCross p q) X =
      (∑ j, QubitOutputForm.rows (p j) (q j) * X * (QubitOutputForm.rows (p j) (q j))ᴴ) +
        Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace) := by
  rw [rows_sum_gram_action]
  have h₀ := Matrix.trace_mul_comm X E₀
  have h₁ := Matrix.trace_mul_comm X E₁
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rowGramAction, Matrix.mul_add, Matrix.trace_add, h₀, h₁]

theorem output_unitary_kraus_complete (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (W : k → Matrix (Fin 2) n ℂ) (hW : (∑ j, (W j)ᴴ * W j) = 1) :
    (∑ j, ((U : Matrix (Fin 2) (Fin 2) ℂ) * W j)ᴴ *
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * W j)) = 1 := by
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  calc
    _ = ∑ j, (W j)ᴴ * W j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (U : Matrix (Fin 2) (Fin 2) ℂ) (W j), hU, Matrix.one_mul]
    _ = 1 := hW

theorem output_unitary_kraus_action (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (W : k → Matrix (Fin 2) n ℂ) (X : Matrix n n ℂ) :
    MatrixMap.of_kraus (fun j => (U : Matrix (Fin 2) (Fin 2) ℂ) * W j)
      (fun j => (U : Matrix (Fin 2) (Fin 2) ℂ) * W j) X =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * MatrixMap.of_kraus W W X *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Every channel with qubit output is the sum of a coherent operation
with at most `dim(input)-1` Kraus operators and two positive commuting-output
effects, in a suitable output basis. -/
theorem exists_qubit_output_rank_decomposition [Nonempty n]
    (Φ : CPTPMap n (Fin 2)) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, ∃ r : ℕ,
    ∃ a b : Fin r → n → ℂ, ∃ E₀ E₁ : Matrix n n ℂ,
      r ≤ Fintype.card n - 1 ∧ E₀.PosSemidef ∧ E₁.PosSemidef ∧
      (∑ j, (vecMulVec (a j) (star (a j)) + vecMulVec (b j) (star (b j)))) +
        E₀ + E₁ = 1 ∧
      ∀ X : Matrix n n ℂ,
        (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X *
            (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
          (∑ j, QubitOutputForm.rows (a j) (b j) * X *
            (QubitOutputForm.rows (a j) (b j))ᴴ) +
          Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace) := by
  obtain ⟨W, hW, hTP⟩ := exists_kraus_family Φ
  let p : (Fin 2 × n) → n → ℂ := fun j i => star (W j 0 i)
  let q : (Fin 2 × n) → n → ℂ := fun j i => star (W j 1 i)
  have hrows : ∀ j, W j = QubitOutputForm.rows (p j) (q j) := by
    intro j
    ext i l
    fin_cases i <;> simp [QubitOutputForm.rows, p, q]
  obtain ⟨s, t, hst, hdet⟩ := exists_rotated_singular_gram p q
  let U : Matrix.unitaryGroup (Fin 2) ℂ := ⟨rotU s t, rotU_mem_unitary hst⟩
  let pr := fun j => star s • p j + star t • q j
  let qr := fun j => -t • p j + s • q j
  have hrot : ∀ j, (U : Matrix (Fin 2) (Fin 2) ℂ) * W j =
      QubitOutputForm.rows (pr j) (qr j) := by
    intro j
    rw [hrows j]
    exact rotU_mul_rows_general s t (p j) (q j)
  have hnorm : rowMass pr + rowMass qr = 1 := by
    rw [← rows_family_gram_complete]
    simpa only [hrot] using output_unitary_kraus_complete U W hTP
  let B := rowCross qr pr
  have hBdet : B.det = 0 := by
    change (rowCross qr pr).det = 0
    rw [← rowCross_conjTranspose pr qr, Matrix.det_conjTranspose]
    simpa only [pr, qr, hdet, star_zero]
  have hblock : (Matrix.fromBlocks (rowMass pr) B Bᴴ (rowMass qr)).PosSemidef := by
    simpa only [B, rowCross_conjTranspose] using rowGram_posSemidef pr qr
  obtain ⟨a, b, hcross, hE₀, hE₁⟩ :=
    PSDFactor.exists_rank_vectors_psd (rowMass pr) (rowMass qr) B hblock
  change rowCross b a = B at hcross
  have hcross' : rowCross a b = rowCross pr qr := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa only [rowCross_conjTranspose, B] using h
  let E₀ := rowMass pr - rowMass a
  let E₁ := rowMass qr - rowMass b
  refine ⟨U, B.rank, a, b, E₀, E₁, rank_le_card_sub_one_of_det_eq_zero B hBdet,
    hE₀, hE₁, ?_, ?_⟩
  · rw [Finset.sum_add_distrib]
    change rowMass a + rowMass b + E₀ + E₁ = 1
    calc
      _ = rowMass pr + rowMass qr := by dsimp [E₀, E₁]; abel
      _ = 1 := hnorm
  · intro X
    have hm := output_unitary_kraus_action U W X
    rw [← hW] at hm
    simp only [hrot, rows_family_gram_action] at hm
    rw [← hm]
    have hp : rowMass pr = rowMass a + E₀ := by dsimp [E₀]; abel
    have hq : rowMass qr = rowMass b + E₁ := by dsimp [E₁]; abel
    rw [hp, hq, ← hcross']
    exact rowGramAction_add_effects a b E₀ E₁ X

theorem rows_sum_padFamily {r s : ℕ} (h : r ≤ s)
    (a b : Fin r → n → ℂ) (X : Matrix n n ℂ) :
    (∑ j, QubitOutputForm.rows (padFamily h a j) (padFamily h b j) * X *
      (QubitOutputForm.rows (padFamily h a j) (padFamily h b j))ᴴ) =
    ∑ j, QubitOutputForm.rows (a j) (b j) * X * (QubitOutputForm.rows (a j) (b j))ᴴ := by
  rw [rows_sum_gram_action, rows_sum_gram_action]
  simp only [rowMass, rowCross, sum_outer_padFamily]

/-- The manuscript's general decomposition lemma, with exactly
`dim(input)-1` slots and zero padding when fewer coherent Kraus operators
suffice. Both residual effects are positive and the formula holds on every
input matrix. -/
theorem exists_qubit_output_decomposition_general [Nonempty n]
    (Φ : CPTPMap n (Fin 2)) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
    ∃ a b : Fin (Fintype.card n - 1) → n → ℂ, ∃ E₀ E₁ : Matrix n n ℂ,
      E₀.PosSemidef ∧ E₁.PosSemidef ∧
      (∑ j, (vecMulVec (a j) (star (a j)) + vecMulVec (b j) (star (b j)))) +
        E₀ + E₁ = 1 ∧
      ∀ X : Matrix n n ℂ,
        (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ.map X *
            (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
          (∑ j, QubitOutputForm.rows (a j) (b j) * X *
            (QubitOutputForm.rows (a j) (b j))ᴴ) +
          Matrix.diagonal (fun i => if i = 0 then (E₀ * X).trace else (E₁ * X).trace) := by
  obtain ⟨U, r, a, b, E₀, E₁, hr, h₀, h₁, hcomplete, hact⟩ :=
    exists_qubit_output_rank_decomposition Φ
  refine ⟨U, padFamily hr a, padFamily hr b, E₀, E₁, h₀, h₁, ?_, ?_⟩
  · simpa only [Finset.sum_add_distrib, sum_outer_padFamily] using hcomplete
  · intro X
    rw [hact X, rows_sum_padFamily]

end SchurEntropy.Qubit
