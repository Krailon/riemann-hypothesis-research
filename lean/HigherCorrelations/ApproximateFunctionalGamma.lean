import HigherCorrelations.ApproximateFunctionalStirlingLimit

/-! UNCONDITIONAL complex Stirling identity on the closed right half-plane,
with an explicit relative error estimate for modulus at least eight. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem afeGamma_stirling_closed (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 2 ≤ ‖z‖) :
    Gamma z = exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection z) := by
  have hn : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hΓ := afeGamma_stirling_identity (z+1) (by simp only [add_re, one_re]; linarith)
    (hnorm.trans (afe_shift_norm z hz 1 (by norm_num)).1)
  have hF := afeStirlingMain_increment_closed z hz hn
  have hC := afeStirlingCorrection_succ z hz hnorm
  have he : afeStirlingMain (z+1) + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection (z+1) = log z +
        (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ) + afeStirlingCorrection z) := by
    linear_combination hF-hC
  rw [Gamma_add_one z hn, he, exp_add, exp_log hn] at hΓ
  exact mul_left_cancel₀ hn hΓ

theorem afeGamma_stirling_relative (z : ℂ) (hz : 0 ≤ z.re) (hnorm : 8 ≤ ‖z‖) :
    ‖Gamma z / exp (afeStirlingMain z + ((Real.log (2*Real.pi)/2:ℝ):ℂ)) - 1‖ ≤
      16/‖z‖ := by
  have hb := afeStirlingCorrection_bound z hz (by linarith)
  have hsmall : ‖afeStirlingCorrection z‖ ≤ 1 := by
    apply hb.trans
    exact (div_le_one (by linarith : 0 < ‖z‖)).mpr hnorm
  rw [afeGamma_stirling_closed z hz (by linarith), exp_add, mul_div_cancel_left₀ _ (exp_ne_zero _)]
  have he := Complex.norm_exp_sub_one_le hsmall
  calc
    _ ≤ 2*‖afeStirlingCorrection z‖ := he
    _ ≤ 2*(8/‖z‖) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end
end HigherCorrelations
