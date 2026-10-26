import HigherCorrelations.TripleMixedDiagonalDefinitions
import HigherCorrelations.TripleBudgetDiagonal

/-! UNCONDITIONAL. Actual coefficient identification, absolute convergence,
and inclusive finite splitting; all prime powers are retained. -/
namespace HigherCorrelations
noncomputable section
open Finset Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonalWeight_knots (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a/(a*b) = a/(b*a) ∧ a/(b*b) = a*b/b^3 := by
  constructor <;> field_simp <;> ring

theorem tripleMixedDiagonal_coefficient (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (n : ℕ) :
    pairMeanPrimeCoefficient a n*pairMeanPrimeCoefficient b n =
      tripleMixedDiagonalWeight a b (n+1)*(Λ (n+1))^2 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hn : 0 < (n+1:ℝ) := by positivity
  have hs := Real.sq_sqrt hn.le
  have hs0 : Real.sqrt (n+1:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have low (x : ℝ) (hx : 0 < x) (h : (n+1:ℝ) ≤ x) :
      min ((n+1:ℝ)/x) (x/(n+1:ℝ)) = (n+1:ℝ)/x := by
    apply min_eq_left
    apply (div_le_div_iff₀ hx hn).mpr
    nlinarith
  have high (x : ℝ) (hx : 0 < x) (h : x ≤ (n+1:ℝ)) :
      min ((n+1:ℝ)/x) (x/(n+1:ℝ)) = x/(n+1:ℝ) := by
    apply min_eq_right
    apply (div_le_div_iff₀ hn hx).mpr
    nlinarith
  rw [pairMeanPrimeCoefficient_sqrt, pairMeanPrimeCoefficient_sqrt]
  unfold tripleMixedDiagonalWeight
  split_ifs with hna hnb
  · rw [low a ha0 hna, low b hb0 (hna.trans hab)]
    field_simp
    nlinarith [hs]
  · rw [high a ha0 (le_of_not_ge hna), low b hb0 hnb]
    field_simp
    nlinarith [hs]
  · rw [high a ha0 (le_of_not_ge hna), high b hb0 (le_of_not_ge hnb)]
    field_simp
    nlinarith [hs]

theorem tripleMixedDiagonalWeight_summable (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun n : ℕ => tripleMixedDiagonalWeight a b n*(Λ n)^2) := by
  apply (summable_nat_add_iff 1).mp
  convert tripleBudgetDiagonal_summable a b ha (ha.trans hab) using 1
  ext n
  simpa only [Nat.cast_add, Nat.cast_one] using (tripleMixedDiagonal_coefficient a b ha hab n).symm

theorem tripleMixedDiagonal_weight (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    tripleBudgetDiagonal a b = ∑' n : ℕ, tripleMixedDiagonalWeight a b n*(Λ n)^2 := by
  rw [(tripleMixedDiagonalWeight_summable a b ha hab).tsum_eq_zero_add]
  simp only [ArithmeticFunction.map_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using tripleMixedDiagonal_coefficient a b ha hab n

theorem tripleMixedDiagonal_partial_tendsto (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 0 N, tripleMixedDiagonalWeight a b n*(Λ n)^2)
      atTop (nhds (tripleBudgetDiagonal a b)) := by
  rw [tripleMixedDiagonal_weight a b ha hab]
  have ht := (tripleMixedDiagonalWeight_summable a b ha hab).hasSum.tendsto_sum_nat
  have hn : Tendsto (fun N : ℕ => N+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  convert ht.comp hn using 1
  funext N
  dsimp only [Function.comp_apply]
  rw [Nat.range_succ_eq_Icc_zero]

theorem tripleMixedDiagonal_finite_split (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2) =
      (1/(a*b))*(∑ n ∈ Icc 0 ⌊a⌋₊, (n:ℝ)*(Λ n)^2)+
      (a/b)*(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Λ n)^2/(n:ℝ))+
      (a*b)*(∑ n ∈ Ioc ⌊b⌋₊ ⌊Y⌋₊, (Λ n)^2/(n:ℝ)^3) := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := ha0.trans hab
  have habf := Nat.floor_le_floor hab
  have hbYf := Nat.floor_le_floor hbY
  have hs : Icc 0 ⌊Y⌋₊ = (Icc 0 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊) ∪ Ioc ⌊b⌋₊ ⌊Y⌋₊ := by
    ext n; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hd1 : Disjoint (Icc 0 ⌊a⌋₊) (Ioc ⌊a⌋₊ ⌊b⌋₊) := by
    apply disjoint_left.mpr; intro n hn hm
    simp only [mem_Icc,mem_Ioc] at *; omega
  have hd2 : Disjoint (Icc 0 ⌊a⌋₊ ∪ Ioc ⌊a⌋₊ ⌊b⌋₊) (Ioc ⌊b⌋₊ ⌊Y⌋₊) := by
    apply disjoint_left.mpr; intro n hn hm
    simp only [mem_union,mem_Icc,mem_Ioc] at *; omega
  rw [hs, sum_union hd2, sum_union hd1, mul_sum, mul_sum, mul_sum]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply sum_congr rfl; intro n hn
      have h : (n:ℝ) ≤ a := (Nat.le_floor_iff ha0).mp (mem_Icc.mp hn).2
      simp [tripleMixedDiagonalWeight,h]; ring
    · apply sum_congr rfl; intro n hn
      have hl : a < (n:ℝ) := (Nat.floor_lt ha0).mp (mem_Ioc.mp hn).1
      have hr : (n:ℝ) ≤ b := (Nat.le_floor_iff hb0).mp (mem_Ioc.mp hn).2
      simp [tripleMixedDiagonalWeight,not_le_of_gt hl,hr]; ring
  · apply sum_congr rfl; intro n hn
    have hl : b < (n:ℝ) := (Nat.floor_lt hb0).mp (mem_Ioc.mp hn).1
    simp [tripleMixedDiagonalWeight,not_le_of_gt hl,not_le_of_gt (hab.trans_lt hl)]; ring
end
end HigherCorrelations
