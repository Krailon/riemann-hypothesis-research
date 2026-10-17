import HigherCorrelations.PairDiagonalDefinitions
import HigherCorrelations.PairMeanPrimeBridge
import Mathlib.NumberTheory.AbelSummation

/-! UNCONDITIONAL. Exact coefficient weights and absolute convergence. -/
namespace HigherCorrelations
noncomputable section
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonalWeight_nonneg (X u : ℝ) (hu : 0 ≤ u) :
    0 ≤ pairDiagonalWeight X u := by unfold pairDiagonalWeight; split_ifs <;> positivity

theorem pairDiagonalWeight_knot (X : ℝ) (hX : 0 < X) :
    X/X^2 = X^2/X^3 := by field_simp

theorem pairMeanPrimeCoefficient_sq_weight (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    pairMeanPrimeCoefficient X n^2 = pairDiagonalWeight X (n+1)*(Λ (n+1))^2 := by
  have hX0 : 0 < X := by linarith
  have hn : 0 < (n+1:ℝ) := by positivity
  have hs := Real.sq_sqrt hn.le
  rw [pairMeanPrimeCoefficient_sqrt]
  unfold pairDiagonalWeight
  split_ifs with h
  · have hm : (n+1:ℝ)/X ≤ X/(n+1:ℝ) := by
      apply (div_le_div_iff₀ hX0 hn).mpr
      nlinarith
    rw [min_eq_left hm, mul_pow, div_pow, hs]
    field_simp
  · have hm : X/(n+1:ℝ) ≤ (n+1:ℝ)/X := by
      apply (div_le_div_iff₀ hn hX0).mpr
      nlinarith [le_of_not_ge h]
    rw [min_eq_right hm, mul_pow, div_pow, hs]
    field_simp
    <;> ring

theorem pairMeanPrimeDiagonal_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n => pairMeanPrimeCoefficient X n^2) := by
  have h := pairFrequency_diagonal_summable (fun n => (pairMeanPrimeCoefficient X n:ℂ))
    (pairMeanPrimeCoefficient_summable X hX)
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem pairMeanPrimePowerDiagonal_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n => if IsPrimePow (n+1) ∧ ¬(n+1).Prime then
      pairMeanPrimeCoefficient X n^2 else 0) := by
  apply Summable.of_nonneg_of_le _ _ (pairMeanPrimeDiagonal_summable X hX)
  · intro n; split_ifs <;> positivity
  · intro n; split_ifs <;> simp [sq_nonneg]

theorem pairMeanPrimeDiagonal_nonneg (X : ℝ) : 0 ≤ pairMeanPrimeDiagonal X :=
  tsum_nonneg fun n => sq_nonneg _

theorem pairMeanPrimePowerDiagonal_nonneg (X : ℝ) : 0 ≤ pairMeanPrimePowerDiagonal X := by
  apply tsum_nonneg
  intro n
  split_ifs <;> positivity

/-- Reindexing to the natural-number API adds only the zero term at n=0. -/
theorem pairDiagonalWeight_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n : ℕ => pairDiagonalWeight X n*(Λ n)^2) := by
  apply (summable_nat_add_iff 1).mp
  convert pairMeanPrimeDiagonal_summable X hX using 1
  ext n
  simpa only [Nat.cast_add, Nat.cast_one] using (pairMeanPrimeCoefficient_sq_weight X hX n).symm

theorem pairMeanPrimeDiagonal_weight (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimeDiagonal X = ∑' n : ℕ, pairDiagonalWeight X n*(Λ n)^2 := by
  rw [(pairDiagonalWeight_summable X hX).tsum_eq_zero_add]
  simp only [ArithmeticFunction.map_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using pairMeanPrimeCoefficient_sq_weight X hX n

/-- No coefficient at the cutoff occurs in the strict upper tail. -/
theorem pairMeanPrimeDiagonal_split (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimeDiagonal X =
      (1/X^2)*(∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n:ℝ)*(Λ n)^2) +
      X^2*(∑' n : ℕ, if X < (n:ℝ) then (Λ n)^2/(n:ℝ)^3 else 0) := by
  have hX0 : 0 < X := by linarith
  let f : ℕ → ℝ := fun n => pairDiagonalWeight X n*(Λ n)^2
  have hf : Summable f := pairDiagonalWeight_summable X hX
  have hf0 (n : ℕ) : 0 ≤ f n := mul_nonneg (pairDiagonalWeight_nonneg X n (Nat.cast_nonneg _)) (sq_nonneg _)
  have hl : Summable (fun n : ℕ => if (n:ℝ) ≤ X then f n else 0) := by
    apply Summable.of_nonneg_of_le _ _ hf
    · intro n; split_ifs <;> simp [hf0]
    · intro n; split_ifs <;> simp [hf0]
  have hr : Summable (fun n : ℕ => if ¬(n:ℝ) ≤ X then f n else 0) := by
    apply Summable.of_nonneg_of_le _ _ hf
    · intro n; split_ifs <;> simp [hf0]
    · intro n; split_ifs <;> simp [hf0]
  have hsum : f = fun n : ℕ => (if (n:ℝ) ≤ X then f n else 0)+
      (if ¬(n:ℝ) ≤ X then f n else 0) := by
    funext n; split_ifs <;> simp_all
  rw [pairMeanPrimeDiagonal_weight X hX]
  change (∑' n, f n) = _
  rw [hsum, Summable.tsum_add hl hr]
  have hlow : (∑' n : ℕ, if (n:ℝ) ≤ X then f n else 0) =
      (1/X^2)*(∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n:ℝ)*(Λ n)^2) := by
    rw [tsum_eq_sum (s := Finset.Icc 0 ⌊X⌋₊)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnX : (n:ℝ) ≤ X := (Nat.le_floor_iff hX0.le).mp (Finset.mem_Icc.mp hn).2
      simp only [hnX, ite_true, f, pairDiagonalWeight]
      ring
    · intro n hn
      have hnX : ¬(n:ℝ) ≤ X := by
        intro h; exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Nat.le_floor_iff hX0.le).mpr h⟩)
      simp [hnX]
  rw [hlow, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  by_cases h : (n:ℝ) ≤ X
  · simp [h, not_lt_of_ge h]
  · simp [h, lt_of_not_ge h, f, pairDiagonalWeight]
    <;> ring

end
end HigherCorrelations
