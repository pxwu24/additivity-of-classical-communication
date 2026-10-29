import SchurEntropy.Results
import QubitAdditivity.BetaTC4Gram

/-!
# The four-block entropy bound from the Schur-weighted block theorem

The coefficient matrix is the all-ones 2 by 2 matrix.  The two row spaces here
have the same positive dimension, as they do for a channel's qubit output.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SchurEntropy.Qubit
open QubitAdditivity
open QubitAdditivity.BetaTC4Gram
open QubitAdditivity.BetaEntropy

variable {R K L T : Type*} [Fintype R] [DecidableEq R]
  [Fintype K] [Fintype L] [Fintype T]

private def twoBlockEquiv (R : Type*) [Fintype R] :
    BlockIndex (fun _ : Fin 2 => Fintype.card R) ≃ R ⊕ R where
  toFun v := if v.1 = 0 then Sum.inl ((Fintype.equivFin R).symm v.2)
    else Sum.inr ((Fintype.equivFin R).symm v.2)
  invFun v := match v with
    | Sum.inl x => ⟨0, Fintype.equivFin R x⟩
    | Sum.inr x => ⟨1, Fintype.equivFin R x⟩
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> simp
  right_inv := by
    intro v
    cases v <;> simp

@[simp] private theorem twoBlockEquiv_zero (a : Fin (Fintype.card R)) :
    twoBlockEquiv R ⟨0, a⟩ = Sum.inl ((Fintype.equivFin R).symm a) := by
  simp [twoBlockEquiv]

@[simp] private theorem twoBlockEquiv_one (a : Fin (Fintype.card R)) :
    twoBlockEquiv R ⟨1, a⟩ = Sum.inr ((Fintype.equivFin R).symm a) := by
  simp [twoBlockEquiv]

private theorem bits_eq_nats {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) : SchurEntropy.entropy X = OpenAIEntropy.entropy X / Real.log 2 := rfl

private theorem entropy_submatrix_equiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : J ≃ I) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    SchurEntropy.entropy (X.submatrix e e) = SchurEntropy.entropy X := by
  change OpenAIEntropy.entropy (X.submatrix e e) / Real.log 2 =
    OpenAIEntropy.entropy X / Real.log 2
  congr 1
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    OpenAIEntropy.entropy_reindex e.symm hX

private theorem entropy_fromBlocks (X Y : Matrix R R ℂ) (hX : X.IsHermitian)
    (hY : Y.IsHermitian) :
    SchurEntropy.entropy (Matrix.fromBlocks X 0 0 Y) =
      SchurEntropy.entropy X + SchurEntropy.entropy Y := by
  have h := QubitAdditivity.BetaDual.psi_diagonal (⟨X, hX⟩, ⟨Y, hY⟩)
  change -OpenAIEntropy.entropy (Matrix.fromBlocks X 0 0 Y) =
    -OpenAIEntropy.entropy X + -OpenAIEntropy.entropy Y at h
  change OpenAIEntropy.entropy (Matrix.fromBlocks X 0 0 Y) / Real.log 2 =
    OpenAIEntropy.entropy X / Real.log 2 + OpenAIEntropy.entropy Y / Real.log 2
  rw [← add_div]
  congr 1
  linarith

private theorem two_blockTrace (X : Matrix (R ⊕ R) (R ⊕ R) ℂ) :
    blockTrace (fun _ : Fin 2 => Fintype.card R)
      (X.submatrix (twoBlockEquiv R) (twoBlockEquiv R)) =
      ![(X.submatrix Sum.inl Sum.inl).trace.re,
        (X.submatrix Sum.inr Sum.inr).trace.re] := by
  funext i
  fin_cases i
  · simpa [blockTrace, twoBlockEquiv, Matrix.trace, Matrix.diag, Complex.re_sum] using
      (Fintype.equivFin R).symm.sum_comp (fun i => (X (Sum.inl i) (Sum.inl i)).re)
  · simpa [blockTrace, twoBlockEquiv, Matrix.trace, Matrix.diag, Complex.re_sum] using
      (Fintype.equivFin R).symm.sum_comp (fun i => (X (Sum.inr i) (Sum.inr i)).re)

private theorem two_pinching (X : Matrix (R ⊕ R) (R ⊕ R) ℂ) :
    pinching (fun _ : Fin 2 => Fintype.card R)
      (X.submatrix (twoBlockEquiv R) (twoBlockEquiv R)) =
      (Matrix.fromBlocks (X.submatrix Sum.inl Sum.inl) 0 0
        (X.submatrix Sum.inr Sum.inr)).submatrix (twoBlockEquiv R) (twoBlockEquiv R) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases i <;> fin_cases j <;>
    simp [pinching_apply, Matrix.submatrix_apply]

private def ones : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun _ _ => 1

private theorem ones_psd : ones.PosSemidef := by
  convert Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 2 => (1 : ℂ)) using 1
  ext i j
  simp [ones, Matrix.vecMulVec_apply]

private theorem schur_ones {n : Fin 2 → ℕ} (H : BlockMatrix n) : blockSchur ones H = H := by
  ext a b
  simp [blockSchur_apply, ones]

private theorem scalar_ones_deficit (x y z w : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    scalarFunction ones ![x, z] ![y, w] =
      SchurEntropy.entropy (tc4ScalarMatrix x y z w) -
        SchurEntropy.entropy (scalarDiagonal ![x, z]) -
        SchurEntropy.entropy (scalarDiagonal ![y, w]) := by
  have hs : scalarSkeleton ones ![x, z] =
      !![(x : ℂ), (Real.sqrt (x*z) : ℂ); (Real.sqrt (x*z) : ℂ), (z : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ones, scalarSkeleton, scalarDiagonal, Matrix.mul_apply, Fin.sum_univ_two,
        ← Complex.ofReal_mul, Real.mul_self_sqrt hx, Real.mul_self_sqrt hz,
        Real.sqrt_mul hx, mul_comm]
  rw [scalarFunction, scalarDeficit, hs]
  congr 2
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tc4ScalarMatrix, scalarDiagonal]
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarDiagonal]

/-- The four-block entropy bound needed for qubit-output channels is a direct
specialization of the manuscript's Schur-weighted block entropy inequality.
No trace normalization is needed for this homogeneous statement. -/
theorem tc4_equal_rows_of_blockEntropy [Nonempty R]
    (A : Matrix R K ℂ) (B : Matrix R L ℂ) (C : Matrix R K ℂ) (D : Matrix R T ℂ) :
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B)
      (blockMass C) (blockMass D)) + weightedBlockEntropy A + weightedBlockEntropy B +
      weightedBlockEntropy C + weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D * (tc4Matrix A B C D)ᴴ) := by
  let n : Fin 2 → ℕ := fun _ => Fintype.card R
  let e := twoBlockEquiv R
  let J := QubitAdditivity.BetaGramSplit.gramPair A C
  let W := QubitAdditivity.BetaDual.diagonal (gramBlocks B D)
  have hJ : J.mat.PosSemidef := gramPair_posSemidef A C
  have hW : W.mat.PosSemidef :=
    QubitAdditivity.BetaDualExistence.diagonal_posSemidef (gramBlocks_mem_positiveCone B D)
  have hdiag : IsBlockDiagonal n (W.mat.submatrix e e) := by
    rw [IsBlockDiagonal, two_pinching]
    rfl
  have hi := block_entropy_inequality 2 n ones
    (J.mat.submatrix e e) (W.mat.submatrix e e) (by decide)
    (fun _ => Fintype.card_pos) ones_psd (hJ.submatrix e) (hW.submatrix e) hdiag
  have htJ : blockTrace n (J.mat.submatrix e e) = ![blockMass A, blockMass C] := by
    rw [two_blockTrace]
    rfl
  have htW : blockTrace n (W.mat.submatrix e e) = ![blockMass B, blockMass D] := by
    rw [two_blockTrace]
    rfl
  have hsum : J.mat + W.mat = tc4Matrix A B C D * (tc4Matrix A B C D)ᴴ := by
    exact (congrArg HermitianMat.mat (gram_tc4Matrix A B C D)).symm
  have hpin : SchurEntropy.entropy (pinching n (J.mat.submatrix e e)) =
      SchurEntropy.entropy (A*Aᴴ) + SchurEntropy.entropy (C*Cᴴ) := by
    rw [two_pinching, entropy_submatrix_equiv _ _
      ((hJ.isHermitian.submatrix Sum.inl).fromBlocks
        (by simp) (hJ.isHermitian.submatrix Sum.inr))]
    exact entropy_fromBlocks _ _ (Matrix.isHermitian_mul_conjTranspose_self A)
      (Matrix.isHermitian_mul_conjTranspose_self C)
  have hnoise : SchurEntropy.entropy (W.mat.submatrix e e) =
      SchurEntropy.entropy (B*Bᴴ) + SchurEntropy.entropy (D*Dᴴ) := by
    rw [entropy_submatrix_equiv _ _ hW.isHermitian]
    exact entropy_fromBlocks _ _ (Matrix.isHermitian_mul_conjTranspose_self B)
      (Matrix.isHermitian_mul_conjTranspose_self D)
  have hreindex : J.mat.submatrix e e + W.mat.submatrix e e =
      (J.mat + W.mat).submatrix e e := rfl
  rw [htJ, htW, scalar_ones_deficit _ _ _ _ (blockMass_nonneg A) (blockMass_nonneg C),
    schur_ones, deficit, hreindex, hsum,
    entropy_submatrix_equiv _ _ (Matrix.isHermitian_mul_conjTranspose_self _), hpin, hnoise] at hi
  have hscalar (v : Fin 2 → ℝ) :
      SchurEntropy.entropy (scalarDiagonal v) = (∑ i, Real.negMulLog (v i)) / Real.log 2 := by
    change OpenAIEntropy.entropy (Matrix.diagonal (fun i => (v i : ℂ))) / Real.log 2 = _
    rw [OpenAIEntropy.entropy_diagonal]
  rw [hscalar, hscalar, Fin.sum_univ_two, Fin.sum_univ_two] at hi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hi
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [weightedBlockEntropy_eq, weightedBlockEntropy_eq, weightedBlockEntropy_eq,
    weightedBlockEntropy_eq]
  simp only [QubitAdditivity.BetaEntropy.psi, neg_neg]
  change OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B)
      (blockMass C) (blockMass D)) +
    (OpenAIEntropy.entropy (A*Aᴴ) + blockMass A * Real.log (blockMass A)) +
    (OpenAIEntropy.entropy (B*Bᴴ) + blockMass B * Real.log (blockMass B)) +
    (OpenAIEntropy.entropy (C*Cᴴ) + blockMass C * Real.log (blockMass C)) +
    (OpenAIEntropy.entropy (D*Dᴴ) + blockMass D * Real.log (blockMass D)) ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D * (tc4Matrix A B C D)ᴴ)
  simp only [bits_eq_nats, Real.negMulLog] at hi
  field_simp [hlog.ne'] at hi
  linarith

end SchurEntropy.Qubit
