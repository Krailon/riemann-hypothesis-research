import HigherCorrelations.ApproximateFunctionalDefinitions
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! UNCONDITIONAL local logarithmic Stirling error. The estimate is quadratic
in the reciprocal modulus, allowing summation along horizontal translates. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem afeStirlingStep_bound (z : ℂ) (hz : 2 ≤ ‖z‖) :
    ‖afeStirlingStep z‖ ≤ 2 / ‖z‖^2 := by
  have hpos : 0 < ‖z‖ := by linarith
  have hne : z ≠ 0 := norm_pos_iff.mp hpos
  have hinv : ‖z⁻¹‖ ≤ 1/2 := by
    rw [norm_inv]
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hz
    simpa only [one_div] using this
  have hTaylor := Complex.norm_log_sub_logTaylor_le 2 (lt_of_le_of_lt hinv (by norm_num))
  have hpoly : logTaylor 3 z⁻¹ = z⁻¹-z⁻¹^2/2 := by
    norm_num [logTaylor_succ, logTaylor_zero]
    ring
  rw [hpoly] at hTaylor
  have hden : (1-‖z⁻¹‖)⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2)
      (show 1/2 ≤ 1-‖z⁻¹‖ by linarith)
    simpa using this
  have herr : ‖log (1+z⁻¹)-(z⁻¹-z⁻¹^2/2)‖ ≤ 2*‖z⁻¹‖^3/3 := by
    apply hTaylor.trans
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    calc
      _ ≤ ‖z⁻¹‖^3 * 2 / 3 := by gcongr
      _ = _ := by ring
  have he : afeStirlingStep z =
      (z+1/2)*(log (1+z⁻¹)-(z⁻¹-z⁻¹^2/2)) - z⁻¹^2/4 := by
    unfold afeStirlingStep
    field_simp [hne]
    ring
  have hcoeff : ‖z+(1/2:ℂ)‖ ≤ ‖z‖+1/2 := by
    simpa using norm_add_le z (1/2:ℂ)
  rw [he]
  have hb := norm_sub_le ((z+1/2)*(log (1+z⁻¹)-(z⁻¹-z⁻¹^2/2))) (z⁻¹^2/4)
  rw [norm_mul, norm_div, norm_pow] at hb
  norm_num at hb
  have hmul := mul_le_mul hcoeff herr (norm_nonneg _) (by positivity : 0 ≤ ‖z‖+1/2)
  simp only [norm_inv, inv_pow] at hmul hb
  have hbase : ‖z‖ * ‖z‖⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hlast : (‖z‖+1/2)*(2*‖z‖⁻¹^3/3)+‖z‖⁻¹^2/4 ≤ 2/‖z‖^2 := by
    field_simp
    nlinarith
  simp only [inv_pow] at hlast
  simp only [inv_pow]
  linarith

theorem afeStirlingMain_increment_closed (z : ℂ) (hz : 0 ≤ z.re) (hn : z ≠ 0) :
    afeStirlingMain (z+1)-afeStirlingMain z = log z + afeStirlingStep z := by
  have hr : 0 < (1+z⁻¹).re := by
    simp only [add_re, one_re, inv_re]
    have hq : 0 ≤ z.re / normSq z := div_nonneg hz (normSq_nonneg z)
    linarith
  have hn' : 1+z⁻¹ ≠ 0 := by intro h; simp [h] at hr
  have ha := abs_le.mp (abs_arg_le_pi_div_two_iff.mpr hz)
  have hb := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  have hlog := Complex.log_mul hn hn' (show arg z + arg (1+z⁻¹) ∈ Set.Ioc (-Real.pi) Real.pi by
    constructor <;> linarith)
  have hmul : z*(1+z⁻¹) = z+1 := by field_simp
  rw [hmul] at hlog
  unfold afeStirlingMain afeStirlingStep
  rw [hlog]
  ring

theorem afeStirlingMain_increment (z : ℂ) (hz : 0 < z.re) :
    afeStirlingMain (z+1)-afeStirlingMain z = log z + afeStirlingStep z := by
  exact afeStirlingMain_increment_closed z hz.le (by intro h; simp [h] at hz)

end
end HigherCorrelations
