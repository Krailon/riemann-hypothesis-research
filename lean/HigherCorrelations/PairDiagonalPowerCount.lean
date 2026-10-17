import HigherCorrelations.PairDiagonalCumulative

/-! UNCONDITIONAL. The proper-power cumulative mass retains its square-root saving. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonalPowerCumulative_eq (u : ℝ) :
    pairDiagonalPowerCumulative u = ∑ n ∈ pairSieveProperPowers ⌊u⌋₊, (Λ n)^2 := by
  unfold pairDiagonalPowerCumulative
  rw [← sum_filter]
  congr 1

theorem pairDiagonalPowerCumulative_nonneg (u : ℝ) : 0 ≤ pairDiagonalPowerCumulative u := by
  rw [pairDiagonalPowerCumulative_eq]
  exact sum_nonneg fun n _ => sq_nonneg _

/-- Inclusive real cutoff, with a constant independent of u. -/
theorem pairDiagonalPowerCumulative_bound (u : ℝ) (hu : 1 ≤ u) :
    pairDiagonalPowerCumulative u ≤ (4/Real.log 2)*Real.sqrt u*Real.log (2*u)^3 := by
  have hu0 : 0 < u := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let N := ⌊u⌋₊
  have hNu : (N:ℝ) ≤ u := Nat.floor_le hu0.le
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hu)
  have hN1 : (N+1:ℝ) ≤ 2*u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog : Real.log 2 ≤ Real.log (2*u) := Real.log_le_log (by norm_num) (by linarith)
  have hlog0 : 0 ≤ Real.log (2*u) := hlog2.le.trans hlog
  have hc : ((pairSieveProperPowers N).card:ℝ) ≤
      (4/Real.log 2)*Real.sqrt u*Real.log (2*u) := by
    have hbase := pairSieveProperPowers_card N
    rw [← Real.sqrt_eq_rpow] at hbase
    have hsqrt : Real.sqrt (N+1:ℝ) ≤ 2*Real.sqrt u := by
      have he := Real.sqrt_le_sqrt hN1
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at he
      have htwo : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
      exact he.trans (mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg _))
    have hfac : 1+Real.log (N+1:ℝ)/Real.log 2 ≤ 2*Real.log (2*u)/Real.log 2 := by
      have hl := Real.log_le_log (by positivity : (0:ℝ)<N+1) hN1
      apply (le_div_iff₀ hlog2).mpr
      have he : (1+Real.log (N+1:ℝ)/Real.log 2)*Real.log 2 = Real.log 2+Real.log (N+1:ℝ) := by field_simp
      rw [he]; linarith
    have hfac0 : 0 ≤ 1+Real.log (N+1:ℝ)/Real.log 2 := by
      have := Real.log_nonneg (show (1:ℝ)≤N+1 by have := Nat.cast_nonneg (α := ℝ) N; linarith)
      positivity
    calc
      _ ≤ Real.sqrt (N+1:ℝ)*(1+Real.log (N+1:ℝ)/Real.log 2) := hbase
      _ ≤ (2*Real.sqrt u)*(2*Real.log (2*u)/Real.log 2) :=
        mul_le_mul hsqrt hfac hfac0 (by positivity)
      _ = _ := by ring
  rw [pairDiagonalPowerCumulative_eq]
  calc
    _ ≤ ∑ n ∈ pairSieveProperPowers N, Real.log (2*u)^2 := by
      apply sum_le_sum
      intro n hn
      have hni := (mem_filter.mp hn).1
      have hn0 : (0:ℝ)<n := by exact_mod_cast (by have := (mem_Icc.mp hni).1; omega : 0<n)
      have hnu : (n:ℝ) ≤ 2*u := (show (n:ℝ)≤N by exact_mod_cast (mem_Icc.mp hni).2).trans (by linarith)
      exact pow_le_pow_left₀ ArithmeticFunction.vonMangoldt_nonneg
        (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnu)) 2
    _ = ((pairSieveProperPowers N).card:ℝ)*Real.log (2*u)^2 := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ((4/Real.log 2)*Real.sqrt u*Real.log (2*u))*Real.log (2*u)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by ring

end
end HigherCorrelations
