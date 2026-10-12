import HigherCorrelations.ProfilePartialFractions

/-! UNCONDITIONAL symmetric finite-interval limits. Individual simple poles are
not assigned whole-line integrals. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem quadratic_ratio_limit (a y : ℝ) :
    Tendsto (fun R : ℝ => ((R-a)^2+y^2)/((-R-a)^2+y^2)) atTop (𝓝 1) := by
  have ha : Tendsto (fun R : ℝ => a * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul a
  have hy : Tendsto (fun R : ℝ => y * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul y
  have hnum := (((tendsto_const_nhds (x := (1 : ℝ))).sub ha).pow 2).add (hy.pow 2)
  have hden := (((tendsto_const_nhds (x := (-1 : ℝ))).sub ha).pow 2).add (hy.pow 2)
  have h : Tendsto (fun R : ℝ => ((1-a*R⁻¹)^2+(y*R⁻¹)^2)/
      ((-1-a*R⁻¹)^2+(y*R⁻¹)^2)) atTop (𝓝 1) := by
    convert hnum.div hden (by norm_num : (-1-(0:ℝ))^2+0^2 ≠ 0) using 1
    norm_num
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  field_simp

theorem quadratic_log_difference_limit (a y : ℝ) (hy : y ≠ 0) :
    Tendsto (fun R : ℝ => Real.log ((R-a)^2+y^2)/2 -
      Real.log ((-R-a)^2+y^2)/2) atTop (𝓝 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp
    (quadratic_ratio_limit a y)
  have hn (R : ℝ) : (R-a)^2+y^2 ≠ 0 := by nlinarith [sq_nonneg (R-a), sq_pos_of_ne_zero hy]
  have hd (R : ℝ) : (-R-a)^2+y^2 ≠ 0 := by nlinarith [sq_nonneg (-R-a), sq_pos_of_ne_zero hy]
  simpa only [Function.comp_def, Real.log_div (hn _) (hd _), sub_div, Real.log_one, zero_div] using h.div_const 2

theorem arctan_difference_limit_pos (a y : ℝ) (hy : 0 < y) :
    Tendsto (fun R : ℝ => Real.arctan ((R-a)/y) - Real.arctan ((-R-a)/y))
      atTop (𝓝 Real.pi) := by
  have ht : Tendsto (fun R : ℝ => (R-a)/y) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [eventually_ge_atTop (K*y+a)] with R hR
    exact (le_div_iff₀ hy).mpr (by linarith)
  have hb : Tendsto (fun R : ℝ => (-R-a)/y) atTop atBot := by
    apply tendsto_atBot.mpr
    intro K
    filter_upwards [eventually_ge_atTop (-K*y-a)] with R hR
    exact (div_le_iff₀ hy).mpr (by linarith)
  have hu := Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds |>.comp ht
  have hl := Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds |>.comp hb
  have he : Real.pi/2 - -(Real.pi/2) = Real.pi := by ring
  simpa only [Function.comp_def, he] using hu.sub hl

theorem arctan_difference_limit_neg (a y : ℝ) (hy : y < 0) :
    Tendsto (fun R : ℝ => Real.arctan ((R-a)/y) - Real.arctan ((-R-a)/y))
      atTop (𝓝 (-Real.pi)) := by
  simpa [div_neg, Real.arctan_neg, sub_eq_add_neg, add_comm] using (arctan_difference_limit_pos a (-y) (by linarith)).neg

theorem simple_pole_truncation_upper (p : ℂ) (hp : 0 < p.im) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, ((x : ℂ)-p)⁻¹)
      atTop (𝓝 (Complex.I * Real.pi)) := by
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (quadratic_log_difference_limit p.re p.im hp.ne')
  have ha := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (arctan_difference_limit_pos p.re p.im hp)
  convert hl.add (ha.const_mul Complex.I) using 1
  · funext R
    simpa using simple_pole_interval p hp.ne' (-R) R
  · simp

theorem simple_pole_truncation_lower (p : ℂ) (hp : p.im < 0) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, ((x : ℂ)-p)⁻¹)
      atTop (𝓝 (-Complex.I * Real.pi)) := by
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (quadratic_log_difference_limit p.re p.im hp.ne)
  have ha := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (arctan_difference_limit_neg p.re p.im hp)
  convert hl.add (ha.const_mul Complex.I) using 1
  · funext R
    simpa using simple_pole_interval p hp.ne (-R) R
  · simp

theorem finite_poles_truncation {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ℂ) (hp : Function.Injective p) (hs : ∀ i, (p i).im ≠ 0) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, (∏ i, ((x : ℂ)-p i))⁻¹) atTop
      (𝓝 (∑ i, poleCoefficient p i * (if 0 < (p i).im then Complex.I*Real.pi else -Complex.I*Real.pi))) := by
  have hi (i : ι) : Continuous (fun x : ℝ => ((x : ℂ)-p i)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x hx
    have him := congrArg Complex.im hx
    simp at him
    exact hs i him
  have hl (i : ι) : Tendsto (fun R : ℝ => poleCoefficient p i * ∫ x : ℝ in -R..R, ((x : ℂ)-p i)⁻¹)
      atTop (𝓝 (poleCoefficient p i * (if 0 < (p i).im then Complex.I*Real.pi else -Complex.I*Real.pi))) := by
    by_cases h : 0 < (p i).im
    · simpa [h] using (simple_pole_truncation_upper (p i) h).const_mul (poleCoefficient p i)
    · simpa [h] using (simple_pole_truncation_lower (p i) (lt_of_le_of_ne (le_of_not_gt h) (hs i))).const_mul (poleCoefficient p i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hl i)
  apply hsum.congr'
  filter_upwards [] with R
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => (hi i).intervalIntegrable (-R) R |>.const_mul (poleCoefficient p i))]
  apply intervalIntegral.integral_congr
  intro x _
  have hx (i : ι) : (x : ℂ) ≠ p i := by
    intro h
    apply hs i
    have hh := congrArg Complex.im h
    simpa using hh.symm
  simpa [poleCoefficient, div_eq_mul_inv] using (simple_pole_partial_fractions p hp (x : ℂ) hx).symm

end
end HigherCorrelations
