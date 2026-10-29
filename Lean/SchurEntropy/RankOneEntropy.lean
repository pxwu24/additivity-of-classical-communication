import SchurEntropy.Isometry
import SchurEntropy.RankOneNormalization
import QuantumInfo.ForMathlib.HermitianMat.CFC

/-
The orthogonal-support argument is adapted from
KitaKen1/qubit-strong-additivity, commit
90e61c463deb42067c109c46f048c6374dfc5945,
lean/QubitAdditivity/BetaOrthogonalEntropy.lean.
Apache-2.0; see third_party/Apache-2.0.txt and third_party/NOTICE.
The proof is restated for matrix entropy in bits with narrowed imports.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace SchurEntropy

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

private theorem entropy_hermitian_cfc (C : HermitianMat ι ℂ) (f : ℝ → ℝ) :
    entropy (C.cfc f).mat =
      (∑ i, Real.negMulLog (f (C.H.eigenvalues i))) / Real.log 2 := by
  have he (B : HermitianMat ι ℂ) :
      entropy B.mat = (B.cfc Real.negMulLog).trace / Real.log 2 := by
    rfl
  rw [he, ← HermitianMat.cfc_comp_apply, HermitianMat.trace_cfc_eq]

/-- Entropy in bits is additive when two Hermitian matrices have orthogonal
supports. This includes singular matrices. -/
theorem entropy_add_of_mul_eq_zero (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A * B = 0) :
    entropy (A + B) = entropy A + entropy B := by
  let AH : HermitianMat ι ℂ := ⟨A, hA⟩
  let BH : HermitianMat ι ℂ := ⟨B, hB⟩
  change entropy (AH + BH).mat = entropy AH.mat + entropy BH.mat
  have hBA : B * A = 0 := by
    have h := congrArg Matrix.conjTranspose hAB
    simpa only [conjTranspose_mul, hA.eq, hB.eq, conjTranspose_zero] using h
  have hc : Commute AH.mat BH.mat := hAB.trans hBA.symm
  obtain ⟨C, ⟨f, hf⟩, ⟨g, hg⟩⟩ := hc.exists_HermitianMat_cfc
  have hAB' : AH.mat * BH.mat = 0 := hAB
  rw [hf, hg] at hAB' ⊢
  have hh : (C.cfc (f * g)).mat = 0 := (C.mat_cfc_mul f g).trans hAB'
  have he : cfc (f * g) C.mat = cfc (fun _ => (0 : ℝ)) C.mat :=
    hh.trans (cfc_const_zero (R := ℝ) (a := C.mat)).symm
  have hcont : ContinuousOn (f * g) (spectrum ℝ C.mat) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_of_discreteTopology
  have hfg := eqOn_of_cfc_eq_cfc he hcont continuousOn_const C.H
  rw [← HermitianMat.cfc_add, entropy_hermitian_cfc, entropy_hermitian_cfc,
    entropy_hermitian_cfc, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h0 : f (C.H.eigenvalues i) * g (C.H.eigenvalues i) = 0 :=
    hfg ((C.H.spectrum_real_eq_range_eigenvalues).symm ▸ Set.mem_range_self i)
  rcases mul_eq_zero.mp h0 with hf | hg
  · simp [hf]
  · simp [hg]

/-- Entropy increments commute with an isometric embedding whenever the
background matrix intertwines with its compressed version. -/
theorem entropy_isometry_increment (V : Matrix κ ι ℂ) (hV : Vᴴ * V = 1)
    (A D : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hD : D.IsHermitian) (hY : Y.IsHermitian)
    (hYV : Y * V = V * D) :
    entropy (V * A * Vᴴ + Y) - entropy Y = entropy (A + D) - entropy D := by
  let B := Y - V * D * Vᴴ
  have hB : B.IsHermitian := hY.sub (isHermitian_mul_mul_conjTranspose V hD)
  have hVY : Vᴴ * Y = D * Vᴴ := by
    have h := congrArg Matrix.conjTranspose hYV
    simpa only [conjTranspose_mul, hY.eq, hD.eq, conjTranspose_conjTranspose] using h
  have hVB : Vᴴ * B = 0 := by
    dsimp only [B]
    rw [Matrix.mul_sub, Matrix.mul_assoc V D Vᴴ, ← Matrix.mul_assoc Vᴴ V (D * Vᴴ), hV, Matrix.one_mul,
      hVY, sub_self]
  have hXB (X : Matrix ι ι ℂ) : (V * X * Vᴴ) * B = 0 := by
    rw [Matrix.mul_assoc, hVB, Matrix.mul_zero]
  have hsum : V * (A + D) * Vᴴ + B = V * A * Vᴴ + Y := by
    dsimp only [B]
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  have hnoise : V * D * Vᴴ + B = Y := by
    dsimp only [B]
    abel
  have h1 := entropy_add_of_mul_eq_zero (V * (A + D) * Vᴴ) B
    (isHermitian_mul_mul_conjTranspose V (hA.add hD)) hB (hXB (A + D))
  have h2 := entropy_add_of_mul_eq_zero (V * D * Vᴴ) B
    (isHermitian_mul_mul_conjTranspose V hD) hB (hXB D)
  rw [hsum, entropy_isometry V hV (A + D) (hA.add hD)] at h1
  rw [hnoise, entropy_isometry V hV D hD] at h2
  rw [h1, h2]
  ring

@[simp] theorem blockMultiplier_conjTranspose {m : ℕ} (n : Fin m → ℕ)
    (y : Fin m → ℝ) : (blockMultiplier n y)ᴴ = blockMultiplier n y := by
  simp [blockMultiplier, Matrix.diagonal_conjTranspose]

/-- Block scalar noise intertwines with the normalized block-column map. -/
theorem blockMultiplier_mul_blockColumns {m : ℕ} {n : Fin m → ℕ}
    (v : BlockIndex n → ℂ) (y : Fin m → ℝ) :
    blockMultiplier n y * blockColumns v = blockColumns v * scalarDiagonal y := by
  ext a i
  simp only [blockMultiplier, scalarDiagonal, diagonal_mul, mul_diagonal, blockColumns]
  split_ifs with h
  · rw [h]
    exact mul_comm _ _
  · simp

/-- The unused dimensions in every block cancel from the entropy increment. -/
theorem entropy_blockColumns_increment {m : ℕ} {n : Fin m → ℕ}
    (v : BlockIndex n → ℂ)
    (hv : ∀ i : Fin m, ∑ a : Fin (n i), star (v ⟨i, a⟩) * v ⟨i, a⟩ = 1)
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.IsHermitian) (y : Fin m → ℝ) :
    entropy (blockColumns v * A * (blockColumns v)ᴴ + blockMultiplier n y)
        - entropy (blockMultiplier n y) =
      entropy (A + scalarDiagonal y) - entropy (scalarDiagonal y) := by
  exact entropy_isometry_increment (blockColumns v) (blockColumns_isometry v hv)
    A (scalarDiagonal y) (blockMultiplier n y) hA
    (scalarDiagonal_conjTranspose y) (blockMultiplier_conjTranspose n y)
    (blockMultiplier_mul_blockColumns v y)

end SchurEntropy
