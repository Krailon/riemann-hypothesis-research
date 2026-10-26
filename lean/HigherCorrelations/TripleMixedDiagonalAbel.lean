import HigherCorrelations.TripleMixedDiagonalAlgebra
import HigherCorrelations.PairDiagonalFinite

/-! UNCONDITIONAL. Finite Abel summation on the middle interval. Both knots
cancel exactly, including coincident knots and prime-power endpoints. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonal_middle_derivative (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => (1:ℝ)/t) (-1/u^2) u := by
  convert (hasDerivAt_const u (1:ℝ)).div (hasDerivAt_id u) hu.ne' using 1 <;> (try funext t) <;> simp [Pi.div_apply]

theorem tripleMixedDiagonal_middle_abel (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Λ n)^2/(n:ℝ)) =
      pairDiagonalCumulative b/b-pairDiagonalCumulative a/a+
        (∫ u in a..b, pairDiagonalCumulative u/u^2) := by
  have hu0 (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := by linarith [hu.1]
  have hd := fun u hu => (tripleMixedDiagonal_middle_derivative u (hu0 u hu)).differentiableAt
  have hi : IntegrableOn (deriv (fun t : ℝ => (1:ℝ)/t)) (Set.Icc a b) := by
    have hc : ContinuousOn (fun t : ℝ => -1/t^2) (Set.Icc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hu0 t ht).ne')
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (tripleMixedDiagonal_middle_derivative t (hu0 t ht)).deriv.symm) measurableSet_Icc
  have he := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => (Λ n)^2)
    (f := fun t : ℝ => 1/t) (show 0 ≤ a by linarith) hab hd hi
  have hid : (∫ t in Set.Ioc a b, deriv (fun u : ℝ => (1:ℝ)/u) t*pairDiagonalCumulative t) =
      -(∫ t in a..b, pairDiagonalCumulative t/t^2) := by
    rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    dsimp only
    rw [(tripleMixedDiagonal_middle_derivative t (hu0 t ht)).deriv]
    ring
  change (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, 1/(n:ℝ)*(Λ n)^2) =
    1/b*pairDiagonalCumulative b-1/a*pairDiagonalCumulative a-
      (∫ t in Set.Ioc a b, deriv (fun u : ℝ => (1:ℝ)/u) t*pairDiagonalCumulative t) at he
  rw [hid] at he
  convert he using 1
  · apply sum_congr rfl; intro n hn; ring
  · ring

theorem tripleMixedDiagonal_finite_abel (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2) =
      a*b*pairDiagonalCumulative Y/Y^3-
      (1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u)+
      (a/b)*(∫ u in a..b, pairDiagonalCumulative u/u^2)+
      3*a*b*(∫ u in b..Y, pairDiagonalCumulative u/u^4) := by
  rw [tripleMixedDiagonal_finite_split a b Y ha hab hbY,
    pairDiagonal_head_abel a ha, tripleMixedDiagonal_middle_abel a b ha hab,
    pairDiagonal_tail_abel b Y (ha.trans hab) hbY]
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  field_simp
  <;> ring

theorem tripleMixedDiagonal_middle_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, Real.log u/u) = (Real.log b^2-Real.log a^2)/2 := by
  have hu0 (u : ℝ) (hu : u ∈ Set.uIcc a b) : 0 < u := by
    rw [Set.uIcc_of_le hab] at hu; exact ha.trans_le hu.1
  have hc : ContinuousOn (fun u : ℝ => Real.log u/u) (Set.uIcc a b) :=
    (Real.continuousOn_log.mono (fun u hu => (hu0 u hu).ne')).div
      continuousOn_id (fun u hu => (hu0 u hu).ne')
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun t : ℝ => Real.log t^2/2) (Real.log u/u) u := by
    convert ((Real.hasDerivAt_log hu.ne').pow 2).div_const 2 using 1 <;> dsimp <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (hu0 u hu)) hc.intervalIntegrable
  convert he using 1 <;> ring

/-- Integrability on finite intervals is established before splitting errors. -/
theorem tripleMixedDiagonal_cumulative_div_integrable (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => pairDiagonalCumulative u/u^k) volume a b := by
  have hi : IntervalIntegrable pairDiagonalCumulative volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (pairDiagonalCumulative_integrable a b ha.le)
  have hc : ContinuousOn (fun u : ℝ => (u^k)⁻¹) (Set.uIcc a b) :=
    (continuousOn_id.pow k).inv₀ (by
      intro u hu; rw [Set.uIcc_of_le hab] at hu
      exact pow_ne_zero _ (ha.trans_le hu.1).ne')
  simpa only [div_eq_mul_inv] using hi.mul_continuousOn hc

theorem tripleMixedDiagonal_error_integral_split (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (k : ℕ) :
    (∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^k) =
      (∫ u in a..b, pairDiagonalCumulative u/u^k)-
      (∫ u in a..b, u*Real.log u/u^k) := by
  have hc : ContinuousOn (fun u : ℝ => u*Real.log u/u^k) (Set.uIcc a b) := by
    have hu0 (u : ℝ) (hu : u ∈ Set.uIcc a b) : u ≠ 0 := by
      rw [Set.uIcc_of_le hab] at hu; exact (ha.trans_le hu.1).ne'
    exact (continuousOn_id.mul (Real.continuousOn_log.mono (fun u hu => hu0 u hu))).div
      (continuousOn_id.pow k) (fun u hu => pow_ne_zero _ (hu0 u hu))
  rw [← intervalIntegral.integral_sub
    (tripleMixedDiagonal_cumulative_div_integrable a b ha hab k) hc.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro u _
  exact sub_div _ _ _

end
end HigherCorrelations
