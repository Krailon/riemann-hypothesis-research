import HigherCorrelations.PairDiagonalIntegrals

/-! UNCONDITIONAL. Finite partial summation on both sides of the moving cutoff. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem pairDiagonalCumulative_integrable (a b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn pairDiagonalCumulative (Set.Icc a b) := by
  have h := integrableOn_mul_sum_Icc (fun n : ℕ => (Λ n)^2) (m := 0) (b := b) ha
    (g := fun _ : ℝ => (1:ℝ)) continuousOn_const.integrableOn_Icc
  unfold pairDiagonalCumulative
  simpa only [one_mul] using h

theorem pairDiagonal_head_abel (X : ℝ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 0 ⌊X⌋₊, (n:ℝ)*(Λ n)^2) =
      X*pairDiagonalCumulative X-∫ u in (1:ℝ)..X, pairDiagonalCumulative u := by
  have he := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => (Λ n)^2) (f := fun t : ℝ => t)
    (by simp) X (fun t _ => differentiableAt_id)
    (by simpa using (continuousOn_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 1 X)))
  simpa only [deriv_id'', one_mul, pairDiagonalCumulative, ← intervalIntegral.integral_of_le hX] using he

theorem pairDiagonal_tail_derivative (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => (1:ℝ)/t^3) (-3/u^4) u := by
  convert (hasDerivAt_const u (1:ℝ)).div ((hasDerivAt_id u).pow 3) (by dsimp; positivity) using 1 <;>
    (try funext t) <;> dsimp <;> field_simp <;> ring

theorem pairDiagonal_tail_abel (X Y : ℝ) (hX : 1 ≤ X) (hXY : X ≤ Y) :
    (∑ n ∈ Ioc ⌊X⌋₊ ⌊Y⌋₊, (Λ n)^2/(n:ℝ)^3) =
      pairDiagonalCumulative Y/Y^3-pairDiagonalCumulative X/X^3+
        3*(∫ u in X..Y, pairDiagonalCumulative u/u^4) := by
  have hu0 (u : ℝ) (hu : u ∈ Set.Icc X Y) : 0 < u := by linarith [hu.1]
  have hd := fun u hu => (pairDiagonal_tail_derivative u (hu0 u hu)).differentiableAt
  have hi : IntegrableOn (deriv (fun t : ℝ => (1:ℝ)/t^3)) (Set.Icc X Y) := by
    have hc : ContinuousOn (fun t : ℝ => -3/t^4) (Set.Icc X Y) :=
      continuousOn_const.div (continuousOn_id.pow 4) (fun t ht => pow_ne_zero _ (hu0 t ht).ne')
    exact hc.integrableOn_Icc.congr_fun
      (fun t ht => (pairDiagonal_tail_derivative t (hu0 t ht)).deriv.symm) measurableSet_Icc
  have he := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ => (Λ n)^2)
    (f := fun t : ℝ => 1/t^3) (show 0 ≤ X by linarith) hXY hd hi
  have hid : (∫ t in Set.Ioc X Y, deriv (fun u : ℝ => (1:ℝ)/u^3) t*pairDiagonalCumulative t) =
      -3*(∫ t in X..Y, pairDiagonalCumulative t/t^4) := by
    rw [← intervalIntegral.integral_of_le hXY, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hXY] at ht
    dsimp only
    rw [(pairDiagonal_tail_derivative t (hu0 t ht)).deriv]
    ring
  change (∑ n ∈ Ioc ⌊X⌋₊ ⌊Y⌋₊, 1/(n:ℝ)^3*(Λ n)^2) =
    1/Y^3*pairDiagonalCumulative Y-1/X^3*pairDiagonalCumulative X-
      (∫ t in Set.Ioc X Y, deriv (fun u : ℝ => (1:ℝ)/u^3) t*pairDiagonalCumulative t) at he
  rw [hid] at he
  convert he using 1
  · apply sum_congr rfl; intro n hn; ring
  · ring

end
end HigherCorrelations
