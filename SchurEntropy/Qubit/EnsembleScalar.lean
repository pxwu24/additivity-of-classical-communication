import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Scalar equality for balanced two-coordinate ensembles

The equality case of the square-root sum bound, including zero coordinate
masses. This is the scalar step in phase-aligning a balanced pure ensemble.
-/

noncomputable section
open scoped BigOperators

namespace SchurEntropy.Qubit

variable {ι : Type*} [Fintype ι]

/-- Proportional nonnegative coordinate masses saturate the square-root
sum bound. The result includes either total mass being zero. -/
theorem sum_sqrt_mul_eq_of_balance
    (x z : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hz : ∀ i, 0 ≤ z i)
    (hbalance : ∀ i, (∑ j, z j) * x i = (∑ j, x j) * z i) :
    (∑ i, Real.sqrt (x i * z i)) = Real.sqrt ((∑ i, x i) * (∑ i, z i)) := by
  classical
  let X := ∑ i, x i
  let Z := ∑ i, z i
  have hXnonneg : 0 ≤ X := Finset.sum_nonneg fun i _ => hx i
  have hZnonneg : 0 ≤ Z := Finset.sum_nonneg fun i _ => hz i
  by_cases hX : X = 0
  · have hxi (i : ι) : x i = 0 := by
      have hi : x i ≤ X := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [hX] using hi) (hx i)
    simp only [hxi, zero_mul, Real.sqrt_zero, Finset.sum_const_zero]
  · have hzi (i : ι) : z i = (Z / X) * x i := by
      apply (mul_left_cancel₀ hX)
      calc
        X * z i = Z * x i := (hbalance i).symm
        _ = X * (Z / X * x i) := by field_simp
    have hs (i : ι) : Real.sqrt (x i * z i) = x i * Real.sqrt (Z / X) := by
      rw [hzi]
      calc
        Real.sqrt (x i * (Z / X * x i)) =
            Real.sqrt ((x i * x i) * (Z / X)) := by congr 1; ring
        _ = x i * Real.sqrt (Z / X) := by
          rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (hx i)]
    calc
      (∑ i, Real.sqrt (x i * z i)) = X * Real.sqrt (Z / X) := by
        simp_rw [hs]
        exact (Finset.sum_mul ..).symm
      _ = Real.sqrt ((X * X) * (Z / X)) := by
        rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hXnonneg]
      _ = Real.sqrt (X * Z) := by congr 1; field_simp

/-- Weighted form of `sum_sqrt_mul_eq_of_balance`. Balance is needed only
for terms with positive probability; zero weights contribute nothing. -/
theorem sum_weighted_sqrt_mul_eq_of_balance
    (p x z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx : ∀ i, 0 ≤ x i) (hz : ∀ i, 0 ≤ z i)
    (hbalance : ∀ i, 0 < p i →
      (∑ j, p j * z j) * x i = (∑ j, p j * x j) * z i) :
    (∑ i, p i * Real.sqrt (x i * z i)) =
      Real.sqrt ((∑ i, p i * x i) * (∑ i, p i * z i)) := by
  have hb (i : ι) : (∑ j, p j * z j) * (p i * x i) =
      (∑ j, p j * x j) * (p i * z i) := by
    by_cases hi : p i = 0
    · simp [hi]
    · have h := hbalance i (lt_of_le_of_ne (hp i) (Ne.symm hi))
      calc
        (∑ j, p j * z j) * (p i * x i) = p i * ((∑ j, p j * z j) * x i) := by ring
        _ = p i * ((∑ j, p j * x j) * z i) := congrArg (fun a => p i * a) h
        _ = (∑ j, p j * x j) * (p i * z i) := by ring
  have h := sum_sqrt_mul_eq_of_balance (fun i => p i * x i) (fun i => p i * z i)
    (fun i => mul_nonneg (hp i) (hx i)) (fun i => mul_nonneg (hp i) (hz i)) hb
  calc
    (∑ i, p i * Real.sqrt (x i * z i)) =
        ∑ i, Real.sqrt ((p i * x i) * (p i * z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (p i * x i) * (p i * z i) = (p i * p i) * (x i * z i) by ring,
        Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (hp i)]
    _ = _ := h

end SchurEntropy.Qubit
