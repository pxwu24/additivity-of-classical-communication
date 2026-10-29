import QubitAdditivity.NormalCommonBranch
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import SchurEntropy.Qubit.RankFactorization

/-!
# Finite-rank extraction from a positive block matrix

The Schur-complement and compactness argument generalizes the rank-one proof
in `QubitAdditivity.NormalSchur` and `QubitAdditivity.NormalCommonBranch`,
KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945 (Apache-2.0).
The factors have exactly as many columns as the rank of the cross block.
-/

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Topology Matrix.Norms.Elementwise
namespace SchurEntropy.Qubit.PSDFactor

variable {n m r : Type*} [Fintype n] [Fintype m] [Fintype r]
variable [DecidableEq n] [DecidableEq m] [DecidableEq r]

/-- The finite-rank Schur-complement construction with a positive definite left block. -/
theorem factor_of_posDef (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (L : Matrix n r ℂ) (R : Matrix m r ℂ)
    (hP : P.PosDef) (hL : Function.Injective L.mulVec)
    (hblock : (Matrix.fromBlocks P (L * Rᴴ) (R * Lᴴ) Q).PosSemidef) :
    ∃ U : Matrix n r ℂ, ∃ V : Matrix m r ℂ,
      U * Vᴴ = L * Rᴴ ∧ (P - U * Uᴴ).PosSemidef ∧ (Q - V * Vᴴ).PosSemidef := by
  let G := Lᴴ * P⁻¹ * L
  have hG : G.PosDef := hP.inv.conjTranspose_mul_mul_same hL
  let S := CFC.sqrt G
  have hS : S.PosSemidef := (CFC.sqrt_nonneg G).posSemidef
  have hSS : S * S = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS.symm ▸ hG.isUnit)
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hSinv : S⁻¹.PosSemidef := hS.inv
  have hSinvSq : S⁻¹ * S⁻¹ = G⁻¹ := by
    rw [← pow_two, inv_pow', pow_two, hSS]
  let := hP.isUnit.invertible
  let := hG.isUnit.invertible
  have hleftBlock : (Matrix.fromBlocks P L Lᴴ G).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₁₁ L G hP).mpr
    exact (show (G - G).PosSemidef by rw [sub_self]; exact Matrix.PosSemidef.zero)
  have hleft := (Matrix.PosDef.fromBlocks₂₂ P L hG).mp hleftBlock
  have hright : (Q - R * G * Rᴴ).PosSemidef := by
    have hb : (Matrix.fromBlocks P (L * Rᴴ) (L * Rᴴ)ᴴ Q).PosSemidef := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hblock
    have h := (Matrix.PosDef.fromBlocks₁₁ (L * Rᴴ) Q hP).mp hb
    simpa only [G, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using h
  refine ⟨L * S⁻¹, R * S, ?_, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, hS.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S, Matrix.nonsing_inv_mul S hSd, Matrix.one_mul]
  · convert hleft using 1
    simp only [Matrix.conjTranspose_mul, hSinv.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S⁻¹ S⁻¹, hSinvSq]
  · convert hright using 1
    simp only [Matrix.conjTranspose_mul, hS.isHermitian.eq, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S S, hSS]

/-- Uniform coordinate bounds supplied by a positive semidefinite Gram residual. -/
theorem norm_bound_of_residual (P : Matrix n n ℂ) {t : ℝ} (ht : t ≤ 1)
    (U : Matrix n r ℂ) (h : (P + t • 1 - U * Uᴴ).PosSemidef) :
    ‖U‖ ≤ ‖fun i => P i i‖ + 1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hi := (Complex.nonneg_iff.mp (h.diag_nonneg (i := i))).1
  have hmul : ((U * Uᴴ) i i).re = ∑ k, ‖U i k‖ ^ 2 := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
  have hj : ‖U i j‖ ^ 2 ≤ ∑ k, ‖U i k‖ ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖U i k‖) (Finset.mem_univ j)
  have hdiag : ‖P i i‖ ≤ ‖fun i => P i i‖ := norm_le_pi_norm (fun i => P i i) i
  have hre := (Complex.re_le_norm (P i i)).trans hdiag
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Complex.real_smul, mul_one, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    hmul] at hi
  norm_num at hi
  nlinarith [norm_nonneg (U i j), norm_nonneg (fun i => P i i)]

/-- Common finite-rank branch extraction, including singular diagonal blocks. -/
theorem factor (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (L : Matrix n r ℂ) (R : Matrix m r ℂ)
    (hL : Function.Injective L.mulVec)
    (hblock : (Matrix.fromBlocks P (L * Rᴴ) (R * Lᴴ) Q).PosSemidef) :
    ∃ U : Matrix n r ℂ, ∃ V : Matrix m r ℂ,
      U * Vᴴ = L * Rᴴ ∧ (P - U * Uᴴ).PosSemidef ∧ (Q - V * Vᴴ).PosSemidef := by
  have hP : P.PosSemidef := by
    convert hblock.submatrix Sum.inl using 1
    ext i j
    rfl
  have hQ : Q.PosSemidef := by
    convert hblock.submatrix Sum.inr using 1
    ext i j
    rfl
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hepos : ∀ j, 0 < e j := fun j => by dsimp [e]; positivity
  have hele : ∀ j, e j ≤ 1 := fun j => by
    dsimp [e]
    rw [div_le_one (by positivity : (0 : ℝ) < (j : ℝ) + 1)]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hex : ∀ j, ∃ U : Matrix n r ℂ, ∃ V : Matrix m r ℂ,
      U * Vᴴ = L * Rᴴ ∧
      (P + e j • 1 - U * Uᴴ).PosSemidef ∧ (Q + e j • 1 - V * Vᴴ).PosSemidef := by
    intro j
    apply factor_of_posDef (P + e j • 1) (Q + e j • 1) L R
      (QubitAdditivity.NormalCommonBranch.posDef_add_identity hP (hepos j)) hL
    rw [QubitAdditivity.NormalCommonBranch.fromBlocks_add_identity]
    exact hblock.add (Matrix.PosSemidef.one.smul (α := ℝ) (hepos j).le)
  choose us vs hc hu hv using hex
  let w : ℕ → (Matrix n r ℂ) × (Matrix m r ℂ) := fun j => (us j, vs j)
  let bound : ℝ := ‖fun i => P i i‖ + ‖fun i => Q i i‖ + 1
  have hbound : ∀ j, w j ∈ Metric.closedBall 0 bound := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    apply max_le_iff.mpr
    constructor
    · exact (norm_bound_of_residual P (hele j) (us j) (hu j)).trans
        (by dsimp [bound]; nlinarith [norm_nonneg (fun i => Q i i)])
    · exact (norm_bound_of_residual Q (hele j) (vs j) (hv j)).trans
        (by dsimp [bound]; nlinarith [norm_nonneg (fun i => P i i)])
  obtain ⟨z, _, f, hf, hz⟩ :=
    (isCompact_closedBall (0 : (Matrix n r ℂ) × (Matrix m r ℂ)) bound).tendsto_subseq hbound
  have he0 : Tendsto (e ∘ f) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hf.tendsto_atTop
  have huz : Tendsto (us ∘ f) atTop (𝓝 z.1) := by
    convert hz.fst_nhds using 1 <;> rfl
  have hvz : Tendsto (vs ∘ f) atTop (𝓝 z.2) := by
    convert hz.snd_nhds using 1 <;> rfl
  have hcross : z.1 * z.2ᴴ = L * Rᴴ := by
    have hccont : Continuous (fun z : (Matrix n r ℂ) × (Matrix m r ℂ) => z.1 * z.2ᴴ) := by
      fun_prop
    have hlim := hccont.continuousAt.tendsto.comp hz
    have hconst : (fun j => us (f j) * (vs (f j))ᴴ) = (fun _ : ℕ => L * Rᴴ) :=
      funext fun j => hc (f j)
    change Tendsto (fun j => us (f j) * (vs (f j))ᴴ) atTop (𝓝 (z.1 * z.2ᴴ)) at hlim
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  refine ⟨z.1, z.2, hcross, ?_, ?_⟩
  · have hcont : Continuous (fun p : ℝ × Matrix n r ℂ => P + p.1 • 1 - p.2 * p.2ᴴ) := by
      fun_prop
    have hlim := hcont.continuousAt.tendsto.comp (he0.prodMk_nhds huz)
    have hres := Matrix.posSemidef_is_closed.mem_of_tendsto hlim
      (Eventually.of_forall fun j => hu (f j))
    simpa using hres
  · have hcont : Continuous (fun p : ℝ × Matrix m r ℂ => Q + p.1 • 1 - p.2 * p.2ᴴ) := by
      fun_prop
    have hlim := hcont.continuousAt.tendsto.comp (he0.prodMk_nhds hvz)
    have hres := Matrix.posSemidef_is_closed.mem_of_tendsto hlim
      (Eventually.of_forall fun j => hv (f j))
    simpa using hres

/-- Every positive two-by-two block matrix has a common branch with exactly
`rank B` columns and positive diagonal residuals. Zero columns may be added. -/
theorem exists_rank_factor_psd (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (B : Matrix n m ℂ)
    (hblock : (Matrix.fromBlocks P B Bᴴ Q).PosSemidef) :
    ∃ U : Matrix n (Fin B.rank) ℂ, ∃ V : Matrix m (Fin B.rank) ℂ,
      U * Vᴴ = B ∧ (P - U * Uᴴ).PosSemidef ∧ (Q - V * Vᴴ).PosSemidef := by
  obtain ⟨L, R, hL, hB⟩ := exists_rank_factor B
  have hb : (Matrix.fromBlocks P (L * Rᴴ) (R * Lᴴ) Q).PosSemidef := by
    simpa only [hB, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hblock
  obtain ⟨U, V, hcross, hP, hQ⟩ := factor P Q L R hL hb
  exact ⟨U, V, hcross.trans hB.symm, hP, hQ⟩

theorem mul_conjTranspose_eq_sum_columns (U : Matrix n r ℂ) (V : Matrix m r ℂ) :
    U * Vᴴ = ∑ s, Matrix.vecMulVec (fun i => U i s) (star (fun j => V j s)) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- Vector form of finite-rank extraction, with the cardinality fixed to `rank B`. -/
theorem exists_rank_vectors_psd (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (B : Matrix n m ℂ)
    (hblock : (Matrix.fromBlocks P B Bᴴ Q).PosSemidef) :
    ∃ a : Fin B.rank → n → ℂ, ∃ b : Fin B.rank → m → ℂ,
      (∑ s, Matrix.vecMulVec (a s) (star (b s))) = B ∧
      (P - ∑ s, Matrix.vecMulVec (a s) (star (a s))).PosSemidef ∧
      (Q - ∑ s, Matrix.vecMulVec (b s) (star (b s))).PosSemidef := by
  obtain ⟨U, V, hUV, hP, hQ⟩ := exists_rank_factor_psd P Q B hblock
  refine ⟨fun s i => U i s, fun s i => V i s, ?_, ?_, ?_⟩
  · rw [← mul_conjTranspose_eq_sum_columns]
    exact hUV
  · rw [← mul_conjTranspose_eq_sum_columns]
    exact hP
  · rw [← mul_conjTranspose_eq_sum_columns]
    exact hQ

end SchurEntropy.Qubit.PSDFactor
