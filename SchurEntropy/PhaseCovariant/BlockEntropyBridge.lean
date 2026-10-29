import SchurEntropy.Results
import SchurEntropy.MultiBlockDiagonal
import SchurEntropy.ScalarConvexityBridge
import QubitAdditivity.Imported.TensorEntropy

/-! # The multiblock entropy estimate on product-indexed matrices

The Schur block theorem is stated on dependent finite index sets and in bits.
This file transports it to arbitrary finite product index sets and entropy in
nats, the convention used by the channel additivity development.
-/

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace SchurEntropy.PhaseCovariant
open QubitAdditivity

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

/-- Schur multiplication of the first (block) indices. -/
def productSchur (C : Matrix d d ℂ) (H : Matrix (d × e) (d × e) ℂ) :
    Matrix (d × e) (d × e) ℂ :=
  (C.submatrix Prod.fst Prod.fst).hadamard H

/-- Direct sum with the block index first, matching tensor-channel matrices. -/
def productDiagonal (W : d → Matrix e e ℂ) : Matrix (d × e) (d × e) ℂ :=
  (Matrix.blockDiagonal' W).submatrix (Equiv.sigmaEquivProd d e).symm
    (Equiv.sigmaEquivProd d e).symm

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
@[simp] theorem productSchur_apply (C : Matrix d d ℂ)
    (H : Matrix (d × e) (d × e) ℂ) (a b : d × e) :
    productSchur C H a b = C a.1 b.1 * H a b := rfl

omit [Fintype d] [Fintype e] [DecidableEq e] in
@[simp] theorem productDiagonal_apply (W : d → Matrix e e ℂ) (a b : d × e) :
    productDiagonal W a b = if a.1 = b.1 then W a.1 a.2 b.2 else 0 := by
  rcases a with ⟨i, a⟩; rcases b with ⟨j, b⟩
  by_cases h : i = j
  · subst j; simp [productDiagonal, Equiv.sigmaEquivProd]
  · simp [productDiagonal, Equiv.sigmaEquivProd, Matrix.blockDiagonal'_apply', h]

/-- Scalar matrix obtained by retaining each block's trace. -/
def traceSkeleton (C : Matrix d d ℂ) (r : d → ℝ) : Matrix d d ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (r i) : ℂ)) * C *
    Matrix.diagonal (fun i => (Real.sqrt (r i) : ℂ))

@[simp] theorem traceSkeleton_apply (C : Matrix d d ℂ) (r : d → ℝ) (i j : d) :
    traceSkeleton C r i j = (Real.sqrt (r i) : ℂ) * C i j * (Real.sqrt (r j) : ℂ) := by
  simp [traceSkeleton, Matrix.diagonal_mul, Matrix.mul_diagonal]

omit [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] in
theorem productSchur_posSemidef {C : Matrix d d ℂ}
    {H : Matrix (d × e) (d × e) ℂ} (hC : C.PosSemidef) (hH : H.PosSemidef) :
    (productSchur C H).PosSemidef :=
  (hC.submatrix Prod.fst).hadamard hH

omit [DecidableEq e] in
theorem productDiagonal_posSemidef {W : d → Matrix e e ℂ}
    (hW : ∀ i, (W i).PosSemidef) : (productDiagonal W).PosSemidef :=
  (MultiBlock.diagonal_posSemidef hW).submatrix _

theorem nats_entropy_submatrix_equiv {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (q : J ≃ I) (X : Matrix I I ℂ)
    (hX : X.IsHermitian) :
    OpenAIEntropy.entropy (X.submatrix q q) = OpenAIEntropy.entropy X := by
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    OpenAIEntropy.entropy_reindex q.symm hX

theorem entropy_productDiagonal (W : d → Matrix e e ℂ)
    (hW : ∀ i, (W i).IsHermitian) :
    OpenAIEntropy.entropy (productDiagonal W) = ∑ i, OpenAIEntropy.entropy (W i) := by
  rw [productDiagonal, nats_entropy_submatrix_equiv _ _
    (Matrix.isHermitian_blockDiagonal'_iff.mpr hW)]
  simp only [OpenAIEntropy.entropy, MultiBlock.cfc_diagonal W hW,
    Matrix.trace_blockDiagonal', Complex.re_sum]

private def finiteProductEquiv (d e : Type*) [Fintype d] [Fintype e] :
    BlockIndex (fun _ : Fin (Fintype.card d) => Fintype.card e) ≃ d × e :=
  (Equiv.sigmaEquivProd _ _).trans
    (Equiv.prodCongr (Fintype.equivFin d).symm (Fintype.equivFin e).symm)

omit [DecidableEq d] [DecidableEq e] in
@[simp] private theorem finiteProductEquiv_apply (i : Fin (Fintype.card d))
    (a : Fin (Fintype.card e)) :
    finiteProductEquiv d e ⟨i, a⟩ =
      ((Fintype.equivFin d).symm i, (Fintype.equivFin e).symm a) := rfl

/-- The block entropy theorem, with scalar entropy corrections expanded and
all entropies measured in nats. No normalization of `H` or `W` is required. -/
theorem block_entropy_product [Nonempty d] [Nonempty e]
    (C : Matrix d d ℂ) (H : Matrix (d × e) (d × e) ℂ)
    (W : d → Matrix e e ℂ) (r y : d → ℝ)
    (hC : C.PosSemidef) (hH : H.PosSemidef) (hW : ∀ i, (W i).PosSemidef)
    (hr : ∀ i, (H.submatrix (fun a => (i, a)) (fun a => (i, a))).trace.re = r i)
    (hy : ∀ i, (W i).trace.re = y i) :
    OpenAIEntropy.entropy (traceSkeleton C r + Matrix.diagonal (fun i => (y i : ℂ)))
      + (∑ i, OpenAIEntropy.entropy
          ((C i i) • H.submatrix (fun a => (i, a)) (fun a => (i, a))))
      - (∑ i, Real.negMulLog ((C i i).re * r i))
      + (∑ i, OpenAIEntropy.entropy (W i))
      - (∑ i, Real.negMulLog (y i))
      ≤ OpenAIEntropy.entropy (productSchur C H + productDiagonal W) := by
  let q := finiteProductEquiv d e
  let v := (Fintype.equivFin d).symm
  let n : Fin (Fintype.card d) → ℕ := fun _ => Fintype.card e
  let Cf := C.submatrix v v
  let Hf : BlockMatrix n := H.submatrix q q
  let Wf : BlockMatrix n := (productDiagonal W).submatrix q q
  have hCf : Cf.PosSemidef := hC.submatrix _
  have hHf : Hf.PosSemidef := hH.submatrix _
  have hWf : Wf.PosSemidef := (productDiagonal_posSemidef hW).submatrix _
  have hbd : IsBlockDiagonal n Wf := by
    rw [isBlockDiagonal_iff]
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    simp only [Wf, Matrix.submatrix_apply, q, finiteProductEquiv_apply,
      productDiagonal_apply, Equiv.apply_eq_iff_eq, hij, ↓reduceIte]
  have htrH : blockTrace n Hf = r ∘ v := by
    funext i
    change (∑ a : Fin (Fintype.card e),
      (H ((Fintype.equivFin d).symm i, (Fintype.equivFin e).symm a)
        ((Fintype.equivFin d).symm i, (Fintype.equivFin e).symm a)).re) = _
    simp only [Function.comp_apply]
    rw [← hr (v i)]
    simpa [Matrix.trace, Complex.re_sum] using
      (Equiv.sum_comp (Fintype.equivFin e).symm
        (fun a => (H (v i, a) (v i, a)).re))
  have htrW : blockTrace n Wf = y ∘ v := by
    funext i
    change (∑ a : Fin (Fintype.card e),
      (productDiagonal W ((Fintype.equivFin d).symm i, (Fintype.equivFin e).symm a)
        ((Fintype.equivFin d).symm i, (Fintype.equivFin e).symm a)).re) = _
    simp only [productDiagonal_apply, ↓reduceIte]
    simp only [Function.comp_apply]
    rw [← hy (v i)]
    simpa [Matrix.trace, Complex.re_sum] using
      (Equiv.sum_comp (Fintype.equivFin e).symm (fun a => (W (v i) a a).re))
  have hJ : blockSchur Cf Hf = (productSchur C H).submatrix q q := by
    ext a b; rfl
  have hsum : blockSchur Cf Hf + Wf =
      (productSchur C H + productDiagonal W).submatrix q q := by
    rw [hJ]; rfl
  have hpinch : pinching n (blockSchur Cf Hf) =
      (productDiagonal (fun i =>
        (C i i) • H.submatrix (fun a => (i, a)) (fun a => (i, a)))).submatrix q q := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [pinching_apply, blockSchur_apply, Cf, Hf, Matrix.submatrix_apply,
      q, finiteProductEquiv_apply, productDiagonal_apply, Equiv.apply_eq_iff_eq,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs with h
    · subst j; rfl
    · rfl
  have hsk : scalarSkeleton Cf (r ∘ v) + scalarDiagonal (y ∘ v) =
      (traceSkeleton C r + Matrix.diagonal (fun i => (y i : ℂ))).submatrix v v := by
    ext i j
    simp [scalarSkeleton, scalarDiagonal, traceSkeleton, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Cf, Matrix.diagonal_apply, v]
  have hrnonneg : ∀ i, 0 ≤ r i := by
    intro i
    rw [← hr i]
    exact (Complex.nonneg_iff.mp (hH.submatrix (fun a => (i, a))).trace_nonneg).1
  have hdiag : Matrix.diagonal (scalarSkeleton Cf (r ∘ v)).diag =
      scalarDiagonal (fun i => (C (v i) (v i)).re * r (v i)) :=
    ScalarConvexity.scalarSkeleton_diagonal ⟨Cf, hCf.1⟩ _ (fun i => hrnonneg (v i))
  have hJP := productSchur_posSemidef hC hH
  have hWP := productDiagonal_posSemidef hW
  have hblock (i : d) :
      ((C i i) • H.submatrix (fun a => (i, a)) (fun a => (i, a))).IsHermitian := by
    exact (hJP.submatrix (fun a => (i, a))).1
  have hpinchedHermitian : (productDiagonal (fun i =>
      (C i i) • H.submatrix (fun a => (i, a)) (fun a => (i, a)))).IsHermitian :=
    (Matrix.isHermitian_blockDiagonal'_iff.mpr hblock).submatrix _
  have hcomparison :
      (traceSkeleton C r + Matrix.diagonal (fun i => (y i : ℂ))).IsHermitian := by
    apply IsHermitian.add
    · have h := isHermitian_mul_mul_conjTranspose
        (Matrix.diagonal (fun i => (Real.sqrt (r i) : ℂ))) hC.1
      have hD : (Matrix.diagonal (fun i => (Real.sqrt (r i) : ℂ))).IsHermitian :=
        isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])
      simpa only [traceSkeleton, hD.eq] using h
    · exact isHermitian_diagonal_iff.mpr (fun i => by simp [IsSelfAdjoint])
  have hb := block_entropy_inequality (Fintype.card d) n Cf Hf Wf
    Fintype.card_pos (fun _ => Fintype.card_pos) hCf hHf hWf hbd
  rw [htrH, htrW] at hb
  unfold scalarFunction scalarDeficit deficit at hb
  rw [hsk, hdiag, hsum, hpinch] at hb
  change OpenAIEntropy.entropy _ / Real.log 2 -
    OpenAIEntropy.entropy _ / Real.log 2 - OpenAIEntropy.entropy _ / Real.log 2 ≤
    OpenAIEntropy.entropy _ / Real.log 2 -
    OpenAIEntropy.entropy _ / Real.log 2 - OpenAIEntropy.entropy _ / Real.log 2 at hb
  dsimp only [Wf] at hb
  rw [nats_entropy_submatrix_equiv v _ hcomparison,
    nats_entropy_submatrix_equiv q _ (hJP.1.add hWP.1),
    nats_entropy_submatrix_equiv q _ hpinchedHermitian,
    nats_entropy_submatrix_equiv q _ hWP.1,
    entropy_productDiagonal _ hblock,
    entropy_productDiagonal _ (fun i => (hW i).1)] at hb
  change OpenAIEntropy.entropy _ / Real.log 2 -
    OpenAIEntropy.entropy (Matrix.diagonal _) / Real.log 2 -
    OpenAIEntropy.entropy (Matrix.diagonal _) / Real.log 2 ≤ _ at hb
  rw [OpenAIEntropy.entropy_diagonal, OpenAIEntropy.entropy_diagonal] at hb
  simp only [Function.comp_apply] at hb
  have hs₁ := Equiv.sum_comp v (fun i => Real.negMulLog ((C i i).re * r i))
  have hs₂ := Equiv.sum_comp v (fun i => Real.negMulLog (y i))
  rw [hs₁, hs₂] at hb
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  field_simp [hlog.ne'] at hb
  linarith

end SchurEntropy.PhaseCovariant
