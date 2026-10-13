import HigherCorrelations.PairedMellinDefinitions

/-! UNCONDITIONAL explicit integrable majorant and upward-line normalization. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairedMellin_denominator_lower (t : ℝ) :
    1+t^2 ≤ ‖(2+(t:ℂ)*Complex.I)^2-1‖ := by
  have hs : (1+t^2)^2 ≤ ‖(2+(t:ℂ)*Complex.I)^2-1‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [sq_nonneg t]
  nlinarith [norm_nonneg ((2+(t:ℂ)*Complex.I)^2-1), sq_nonneg t]

theorem pairedMellin_denominator_ne_zero (t : ℝ) : (2+(t:ℂ)*Complex.I)^2-1 ≠ 0 := by
  intro h
  have hb := pairedMellin_denominator_lower t
  rw [h,norm_zero] at hb
  nlinarith [sq_nonneg t]

theorem pairedMellinIntegrand_bound (y t : ℝ) (hy : 0<y) :
    ‖pairedMellinIntegrand y t‖ ≤ 2*y^2/(1+t^2) := by
  have he : ‖Complex.exp ((2+(t:ℂ)*Complex.I)*(Real.log y:ℂ))‖ = y^2 := by
    rw [Complex.norm_exp]
    have hr : ((2+(t:ℂ)*Complex.I)*(Real.log y:ℂ)).re = 2*Real.log y := by
      simp [Complex.mul_re]
    rw [hr]
    rw [show 2*Real.log y = Real.log y+Real.log y by ring, Real.exp_add, Real.exp_log hy]
    ring
  unfold pairedMellinIntegrand
  rw [norm_div, norm_mul, he]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pairedMellin_denominator_lower t)

theorem pairedMellinIntegrand_continuous (y : ℝ) : Continuous (pairedMellinIntegrand y) := by
  exact (by fun_prop : Continuous (fun t : ℝ => 2*Complex.exp ((2+(t:ℂ)*Complex.I)*(Real.log y:ℂ)))).div
    (by fun_prop) pairedMellin_denominator_ne_zero

theorem pairedMellinIntegrand_integrable (y : ℝ) (hy : 0<y) : Integrable (pairedMellinIntegrand y) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul (2*y^2))
    (pairedMellinIntegrand_continuous y).aestronglyMeasurable
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using pairedMellinIntegrand_bound y t hy

theorem pairedMellin_upward_integrable (y : ℝ) (hy : 0<y) :
    Integrable (fun t => pairedMellinIntegrand y t * Complex.I) :=
  (pairedMellinIntegrand_integrable y hy).mul_const Complex.I

theorem pairedMellinSymbol_vertical : Complex.VerticalIntegrable pairedMellinSymbol 2 := by
  unfold Complex.VerticalIntegrable
  convert pairedMellinIntegrand_integrable 1 (by norm_num) using 1
  ext t
  simp [pairedMellinIntegrand, pairedMellinSymbol]

theorem pairedMellin_upward_normalization (y : ℝ) :
    pairedMellinUpwardIntegral y = pairedMellinKernel y := by
  unfold pairedMellinUpwardIntegral pairedMellinKernel
  rw [integral_mul_const]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  field_simp

theorem pairedMellin_truncation_limit (y : ℝ) (hy : 0<y) :
    Tendsto (pairedMellinTruncation y) atTop (𝓝 (pairedMellinKernel y)) := by
  exact (intervalIntegral_tendsto_integral (pairedMellinIntegrand_integrable y hy)
    tendsto_neg_atTop_atBot tendsto_id).const_smul (1/(2*Real.pi) : ℝ)

end
end HigherCorrelations
