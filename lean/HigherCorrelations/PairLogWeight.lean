import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! An explicit integrable majorant for the logarithmic vertical weight. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairLogWeight_bound (t v : ℝ) :
    Real.log (|v|+2)/(1+(v-t)^2) ≤
      (Real.log (|t|+3)+4)*(1+(v-t)^2)^(-(3/4:ℝ)) := by
  let y := 1+(v-t)^2
  have hy : 1 ≤ y := by dsimp [y]; nlinarith [sq_nonneg (v-t)]
  have hy0 : 0 < y := by linarith
  have hc : 0 < |t|+3 := by positivity
  have hb : |v|+2 ≤ (|t|+3)*y := by
    have hh := abs_add_le (v-t) t
    rw [sub_add_cancel] at hh
    have hw : |v-t| ≤ 1+(v-t)^2 := by nlinarith [sq_nonneg (|v-t|-1),sq_abs (v-t)]
    have ha := abs_nonneg t
    dsimp [y] at *
    nlinarith [mul_nonneg (abs_nonneg t) (sq_nonneg (v-t))]
  have hlog := Real.log_le_log (by positivity : 0 < |v|+2) hb
  rw [Real.log_mul hc.ne' hy0.ne'] at hlog
  have hp : 1 ≤ y^(1/4:ℝ) := Real.one_le_rpow hy (by norm_num)
  have hl : Real.log y ≤ 4*y^(1/4:ℝ) := by
    have := Real.log_le_rpow_div hy0.le (by norm_num : (0:ℝ)<1/4)
    linarith
  have hc0 : 0 ≤ Real.log (|t|+3) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  have hh : Real.log (|v|+2) ≤ (Real.log (|t|+3)+4)*y^(1/4:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hp hc0]
  change Real.log (|v|+2)/y ≤ _
  apply (div_le_div_of_nonneg_right hh hy0.le).trans_eq
  change (Real.log (|t|+3)+4)*y^(1/4:ℝ)/y = (Real.log (|t|+3)+4)*y^(-(3/4:ℝ))
  rw [mul_div_assoc]
  have he : y^(1/4:ℝ)/y = y^(-(3/4:ℝ)) := by
    nth_rw 2 [← Real.rpow_one y]
    rw [← Real.rpow_sub hy0]
    norm_num
  rw [he]

theorem pairLogWeight_integrable (t : ℝ) :
    Integrable (fun v : ℝ => Real.log (|v|+2)/(1+(v-t)^2)) := by
  have hp : Integrable (fun v : ℝ => (1+v^2)^(-(3/4:ℝ))) := by
    convert (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 3/2) (by norm_num)) using 1
    ext v
    simp [Real.norm_eq_abs, sq_abs]
    norm_num
  apply ((hp.comp_sub_right t).const_mul (Real.log (|t|+3)+4)).mono'
    (Measurable.aestronglyMeasurable (by fun_prop))
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact pairLogWeight_bound t v
  · exact div_nonneg (Real.log_nonneg (by have := abs_nonneg v; linarith)) (by positivity)

end
end HigherCorrelations
