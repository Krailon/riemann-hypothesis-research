import HigherCorrelations.ApproximateFunctionalHankel
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! UNCONDITIONAL control of the shrinking circle in the initial Hankel
representation. The limit fixes s and the integer cutoff m, and requires Re(s)>1. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology

theorem afe_exp_small_denominator (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖z‖/2 ≤ ‖exp z-1‖ := by
  have he := norm_exp_sub_one_sub_id_le (show ‖z‖ ≤ 1 by linarith)
  have ht := norm_sub_norm_le z (exp z-1)
  rw [norm_sub_rev z (exp z-1)] at ht
  nlinarith [norm_nonneg z]

theorem afeHankelPower_bound (s z : ℂ) (hz : z ≠ 0) :
    ‖afeHankelPower s z‖ ≤ ‖z‖^(s.re-1)*Real.exp (2*Real.pi*|s.im|) := by
  rw [afeHankelPower_norm s z hz]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply Real.exp_le_exp.mpr
  have ha := neg_pi_lt_arg (-z)
  have hb := arg_le_pi (-z)
  calc
    -s.im*(arg (-z)+Real.pi) ≤ |s.im| *(arg (-z)+Real.pi) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) (by linarith)
    _ ≤ |s.im| *(2*Real.pi) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = _ := by ring

theorem afeHankelKernel_small_bound (s : ℂ) (m : ℕ) (z : ℂ)
    (hz : z ≠ 0) (hr : ‖z‖ ≤ 1/2) :
    ‖afeHankelKernel s m z‖ ≤
      2*‖z‖^(s.re-1)/‖z‖*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2) := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hd := afe_exp_small_denominator z hr
  have he : ‖exp (-(m:ℂ)*z)‖ ≤ Real.exp ((m:ℝ)/2) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (-(m:ℂ)*z).re ≤ ‖-(m:ℂ)*z‖ := re_le_norm _
      _ = (m:ℝ)*‖z‖ := by simp
      _ ≤ (m:ℝ)/2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  rw [afeHankelKernel, norm_div, norm_mul]
  calc
    _ ≤ (‖z‖^(s.re-1)*Real.exp (2*Real.pi*|s.im|)*Real.exp ((m:ℝ)/2)) /
        (‖z‖/2) := div_le_div₀ (by positivity)
          (mul_le_mul (afeHankelPower_bound s z hz) he (norm_nonneg _) (by positivity))
          (by positivity) hd
    _ = _ := by rw [Real.exp_add]; ring

theorem afeHankelKernel_measurable (s : ℂ) (m : ℕ) :
    Measurable (afeHankelKernel s m) := by
  unfold afeHankelKernel afeHankelPower afeHankelLog
  fun_prop

theorem afeHankel_circle_bound (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    ‖∮ z in C(0,r), afeHankelKernel s m z‖ ≤
      4*Real.pi*r^(s.re-1)*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2) := by
  have h := circleIntegral.norm_integral_le_of_norm_le_const hr.le
    (f := afeHankelKernel s m) (c := 0)
    (C := 2*r^(s.re-1)/r*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2)) (fun z hz => by
      have hn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hz' : z ≠ 0 := norm_pos_iff.mp (hn ▸ hr)
      simpa only [hn] using afeHankelKernel_small_bound s m z hz' (hn ▸ hr'))
  convert h using 1
  field_simp
  <;> ring

theorem afeHankel_circle_integrable (s : ℂ) (m : ℕ) (r : ℝ)
    (hr : 0 < r) (hr' : r ≤ 1/2) :
    CircleIntegrable (afeHankelKernel s m) 0 r := by
  rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  refine Integrable.of_bound
    ((afeHankelKernel_measurable s m).comp (continuous_circleMap 0 r).measurable
      |>.aestronglyMeasurable) (2*r^(s.re-1)/r*
        Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2)) (ae_of_all _ fun θ => ?_)
  have hn : ‖circleMap 0 r θ‖ = r := by simp [circleMap, abs_of_pos hr]
  simpa only [hn] using afeHankelKernel_small_bound s m (circleMap 0 r θ)
    (norm_pos_iff.mp (by rw [hn]; exact hr)) (by rw [hn]; exact hr')

theorem afeHankel_circle_tendsto_zero (s : ℂ) (hs : 1 < s.re) (m : ℕ) :
    Tendsto (fun r : ℝ => ∮ z in C(0,r), afeHankelKernel s m z) (𝓝[>] 0) (𝓝 0) := by
  have hp : 0 < s.re-1 := by linarith
  have hr : Tendsto (fun r : ℝ => r^(s.re-1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const 0 (s.re-1) (Or.inr hp.le)).tendsto.mono_left
        nhdsWithin_le_nhds
  have hB : Tendsto (fun r : ℝ =>
      4*Real.pi*r^(s.re-1)*Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hr.const_mul (4*Real.pi)).mul_const
      (Real.exp (2*Real.pi*|s.im|+(m:ℝ)/2))
  apply squeeze_zero_norm' _ hB
  filter_upwards [self_mem_nhdsWithin, eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)
    |>.filter_mono nhdsWithin_le_nhds] with r hr hr'
  exact afeHankel_circle_bound s m r hr hr'.le

end
end HigherCorrelations
