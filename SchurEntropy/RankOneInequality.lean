import SchurEntropy.RankOneNormalization
import SchurEntropy.RankOneEntropy
import SchurEntropy.EntropyIncrement
import SchurEntropy.BlockTraceBound

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace SchurEntropy

/-- The Schur-weighted block entropy inequality for a rank-one positive
input, including vanishing block vectors and singular noise. -/
theorem rankOne_block_entropy {m : ℕ} {n : Fin m → ℕ}
    (hn : ∀ i, 0 < n i) (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : C.PosSemidef) (u : BlockIndex n → ℂ) (W : BlockMatrix n)
    (hW : W.PosSemidef) (hdiag : IsBlockDiagonal n W) :
    scalarFunction C (blockTrace n (outerProduct u)) (blockTrace n W) ≤
      deficit n (blockSchur C (outerProduct u)) W := by
  obtain ⟨v, hv, hscale⟩ := exists_block_normalization hn u
  let A := scalarSkeleton C (blockTrace n (outerProduct u))
  let J := blockSchur C (outerProduct u)
  have hA : A.PosSemidef := scalarSkeleton_posSemidef hC _
  have hJ : J.PosSemidef := blockSchur_posSemidef hC
    (Matrix.posSemidef_vecMulVec_self_star u)
  have hu : u = fun a => (Real.sqrt (blockTrace n (outerProduct u) a.1) : ℂ) * v a :=
    funext hscale
  have hJA : J = blockColumns v * A * (blockColumns v)ᴴ := by
    change blockSchur C (outerProduct u) = _
    conv_lhs => rw [hu]
    exact blockSchur_outerProduct_scaled v C _
  have hpin : entropy (pinching n J) = entropy (Matrix.diagonal A.diag) := by
    rw [hJA, pinching_blockColumns]
    exact entropy_isometry (blockColumns v) (blockColumns_isometry v hv) _
      (Matrix.PosSemidef.diagonal (fun i => hA.diag_nonneg)).isHermitian
  have hi := entropy_increment_antitone hJ hW
    (blockMultiplier_blockTrace_sub_posSemidef hW hdiag)
  have he := entropy_blockColumns_increment v hv A hA.isHermitian (blockTrace n W)
  rw [← hJA] at he
  rw [he] at hi
  change entropy (A + scalarDiagonal (blockTrace n W)) -
    entropy (Matrix.diagonal A.diag) - entropy (scalarDiagonal (blockTrace n W)) ≤
    entropy (J + W) - entropy (pinching n J) - entropy W
  rw [hpin]
  linarith

end SchurEntropy
