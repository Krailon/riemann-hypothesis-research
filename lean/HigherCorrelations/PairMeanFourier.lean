import HigherCorrelations.PairMeanSeries
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL bridge to mathlib's Fourier transform in cycles, with
the interval-indicator transform computed at zero as well as away from zero. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex
open scoped FourierTransform

theorem pairMeanFourier_eq (f : ℝ → ℂ) (ξ : ℝ) : pairMeanFourier f ξ = 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold pairMeanFourier
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [pairMeanCharacter, smul_eq_mul]
  congr 2
  push_cast
  ring

theorem pairMeanFourier_norm_bound (f : ℝ → ℂ) (ξ : ℝ) :
    ‖pairMeanFourier f ξ‖ ≤ ∫ t : ℝ, ‖f t‖ := by
  have h := norm_integral_le_integral_norm (μ := volume) (fun t => pairMeanCharacter (-t*ξ)*f t)
  simpa only [pairMeanFourier, norm_mul, pairMeanCharacter_norm, one_mul] using h

theorem pairMeanBox_integrable : Integrable pairMeanBox := by
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (show IntegrableOn (fun _ : ℝ => (1:ℂ)) (Set.Icc (-(1/2:ℝ)) (1/2)) from
      continuous_const.integrableOn_Icc)

theorem pairMeanBox_fourier (ξ : ℝ) : pairMeanFourier pairMeanBox ξ = (pairMeanSinc ξ:ℂ) := by
  have hi : pairMeanFourier pairMeanBox ξ =
      ∫ t : ℝ in -(1/2:ℝ)..(1/2), exp ((-2*(Real.pi:ℂ)*I*ξ)*t) := by
    unfold pairMeanFourier pairMeanBox
    have he : (fun t : ℝ => pairMeanCharacter (-t*ξ)*
        Set.indicator (Set.Icc (-(1/2:ℝ)) (1/2)) (fun _ => (1:ℂ)) t) =
        Set.indicator (Set.Icc (-(1/2:ℝ)) (1/2))
          (fun t : ℝ => exp ((-2*(Real.pi:ℂ)*I*ξ)*t)) := by
      funext t
      by_cases ht : t ∈ Set.Icc (-(1/2:ℝ)) (1/2)
      · simp only [Set.indicator_of_mem ht, mul_one, pairMeanCharacter]
        congr 1
        push_cast
        ring
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ) ≤ 1/2)]
  rw [hi]
  by_cases hξ : ξ = 0
  · subst ξ
    norm_num [pairMeanSinc]
  · have hn : (-2*(Real.pi:ℂ)*I*ξ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (Complex.ofReal_ne_zero.mpr hξ)
    rw [integral_exp_mul_complex hn]
    have hplus : (-2*(Real.pi:ℂ)*I*ξ)*(1/2:ℝ) = -((Real.pi:ℂ)*ξ)*I := by push_cast; ring
    have hminus : (-2*(Real.pi:ℂ)*I*ξ)*(-(1/2:ℝ)) = ((Real.pi:ℂ)*ξ)*I := by push_cast; ring
    rw [hplus, Complex.ofReal_neg, hminus, exp_mul_I,exp_mul_I,cos_neg,sin_neg]
    unfold pairMeanSinc
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hξ)]
    push_cast
    field_simp
    ring

end
end HigherCorrelations
