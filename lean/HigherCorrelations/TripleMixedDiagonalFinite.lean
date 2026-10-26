import HigherCorrelations.TripleMixedDiagonalAbel

/-! UNCONDITIONAL. Exact finite model and uniform error bounds. The upper
cutoff remains finite throughout this module. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonal_finite_error_identity (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2)-
      (tripleMixedDiagonalModel a b-a*b*(2*Real.log Y+3)/(4*Y^2)) =
      a*b*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3-
      (1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u-u*Real.log u)+
      (a/b)*(∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2)+
      3*a*b*(∫ u in b..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hY0 : 0 < Y := hb0.trans_le hbY
  have hA : IntervalIntegrable pairDiagonalCumulative volume 1 a :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha).mpr
      (pairDiagonalCumulative_integrable 1 a zero_le_one)
  have hM : IntervalIntegrable (fun u : ℝ => u*Real.log u) volume 1 a := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.mul (Real.continuousOn_log.mono _)
    intro u hu; rw [Set.uIcc_of_le ha] at hu; exact ne_of_gt (by linarith [hu.1])
  have hm2 : (∫ u in a..b, u*Real.log u/u^2) = ∫ u in a..b, Real.log u/u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by rw [Set.uIcc_of_le hab] at hu; linarith [hu.1]
    dsimp; field_simp
  have hm4 : (∫ u in b..Y, u*Real.log u/u^4) = ∫ u in b..Y, Real.log u/u^3 := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : u ≠ 0 := by rw [Set.uIcc_of_le hbY] at hu; linarith [hu.1]
    dsimp; field_simp
  rw [tripleMixedDiagonal_finite_abel a b Y ha hab hbY,
    intervalIntegral.integral_sub hA hM,
    tripleMixedDiagonal_error_integral_split a b ha0 hab 2,
    tripleMixedDiagonal_error_integral_split b Y hb0 hbY 4, hm2, hm4,
    pairDiagonal_head_integral a ha, tripleMixedDiagonal_middle_integral a b ha0 hab,
    pairDiagonal_tail_integral b Y hb0 hbY]
  unfold tripleMixedDiagonalModel tripleMixedDiagonalMain
  rw [Real.log_div hb0.ne' ha0.ne', Real.log_mul ha0.ne' hb0.ne']
  field_simp
  <;> ring

theorem tripleMixedDiagonal_middle_error (K a b : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2| ≤ K*Real.log (b/a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hc : ContinuousOn (fun u : ℝ => K/u) (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id (by
      intro u hu; rw [Set.uIcc_of_le hab] at hu; exact (ha0.trans_le hu.1).ne')
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
    (f := fun u : ℝ => (pairDiagonalCumulative u-u*Real.log u)/u^2)
    (g := fun u : ℝ => K/u) (Filter.Eventually.of_forall (by
      intro u hu
      have hu0 : 0 < u := ha0.trans hu.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hu0 2)]
      calc
        _ ≤ K*u/u^2 := div_le_div_of_nonneg_right (hE u (ha.trans hu.1.le)) (by positivity)
        _ = _ := by field_simp)) hc.intervalIntegrable
  have hi : (∫ u in a..b, K/u) = K*Real.log (b/a) := by
    have hd : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => K*Real.log t) (K/u) u := by
      intro u hu
      have hu0 : u ≠ 0 := by rw [Set.uIcc_of_le hab] at hu; linarith [hu.1]
      convert (Real.hasDerivAt_log hu0).const_mul K using 1 <;> simp [div_eq_mul_inv]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
      Real.log_div hb0.ne' ha0.ne']
    ring
  simpa only [Real.norm_eq_abs,hi] using hb

/-- The bound is uniform in a,b,Y. Its cumulative constant is explicit input. -/
theorem tripleMixedDiagonal_finite_error_bound (K a b Y : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |(∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2)-
      (tripleMixedDiagonalModel a b-a*b*(2*Real.log Y+3)/(4*Y^2))| ≤
      K*(a/b)*(3+Real.log (b/a)) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hY0 : 0 < Y := hb0.trans_le hbY
  have hh0 := (pairDiagonal_error_integrals K a b hK ha hab hE).1
  have ht0 := (pairDiagonal_error_integrals K b Y hK (ha.trans hab) hbY hE).2
  have hm0 := tripleMixedDiagonal_middle_error K a b hK ha hab hE
  have hb : |a*b*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3| ≤ K*(a/b) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos ha0 hb0), abs_of_pos (pow_pos hY0 3)]
    calc
      _ ≤ a*b*(K*Y)/Y^3 := by gcongr; exact hE Y (ha.trans (hab.trans hbY))
      _ = (K*a)*(b/Y^2) := by field_simp <;> ring
      _ ≤ (K*a)*(1/b) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_div_iff₀ (sq_pos_of_pos hY0) hb0).mpr
        nlinarith
      _ = _ := by ring
  have hh : |(1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u-u*Real.log u)| ≤ K*(a/b)/2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1/(a*b))]
    calc
      _ ≤ (1/(a*b))*(K*a^2/2) := mul_le_mul_of_nonneg_left hh0 (by positivity)
      _ = _ := by field_simp
  have hm : |(a/b)*(∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2)| ≤
      K*(a/b)*Real.log (b/a) := by
    rw [abs_mul, abs_of_pos (div_pos ha0 hb0)]
    exact (mul_le_mul_of_nonneg_left hm0 (by positivity)).trans_eq (by ring)
  have ht : |3*a*b*(∫ u in b..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4)| ≤ 3*K*(a/b)/2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 3*a*b)]
    calc
      _ ≤ (3*a*b)*(K/(2*b^2)) := mul_le_mul_of_nonneg_left ht0 (by positivity)
      _ = _ := by field_simp <;> ring
  rw [tripleMixedDiagonal_finite_error_identity a b Y ha hab hbY]
  calc
    _ ≤ (|a*b*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3|+
        |(1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u-u*Real.log u)|)+
        |(a/b)*(∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2)|+
        |3*a*b*(∫ u in b..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4)| := by
      exact (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ (K*(a/b)+K*(a/b)/2)+K*(a/b)*Real.log (b/a)+3*K*(a/b)/2 :=
      add_le_add (add_le_add (add_le_add hb hh) hm) ht
    _ = _ := by ring

end
end HigherCorrelations
