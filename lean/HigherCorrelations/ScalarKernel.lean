import HigherCorrelations.IntegralProfileDefinitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! UNCONDITIONAL scalar denominator bounds on an enlarged horizontal strip. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem scalar_denominator_lower (x e : ℝ) (he : |e| ≤ 3/4) :
    (7/16 : ℝ) * (1+x^2) ≤ ‖1 + ((x : ℂ) + Complex.I * e)^2‖ := by
  have h := Complex.re_le_norm (1 + ((x : ℂ) + Complex.I * e)^2)
  have hr : (1 + ((x : ℂ) + Complex.I * e)^2).re = 1+x^2-e^2 := by
    simp [pow_two, Complex.mul_re]; ring
  rw [hr] at h
  rcases abs_le.mp he with ⟨hl,hu⟩
  nlinarith [sq_nonneg x]

theorem scalar_denominator_ne_zero (x e : ℝ) (he : |e| ≤ 3/4) :
    1 + ((x : ℂ) + Complex.I * e)^2 ≠ 0 := by
  intro h
  have hb := scalar_denominator_lower x e he
  rw [h, norm_zero] at hb
  nlinarith [sq_nonneg x]

theorem scalarKernel_bound (x e : ℝ) (he : |e| ≤ 3/4) :
    ‖scalarKernel x e‖ ≤ 4 / (1+x^2) := by
  have hp : 0 < 1+x^2 := by positivity
  have hb := scalar_denominator_lower x e he
  have hn : 0 < ‖1 + ((x : ℂ) + Complex.I * e)^2‖ := by nlinarith
  rw [scalarKernel, norm_inv]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hn hp).mpr
  nlinarith

theorem scalarKernel_continuous (e : ℝ) (he : |e| ≤ 3/4) : Continuous (fun x => scalarKernel x e) := by
  unfold scalarKernel
  apply Continuous.inv₀ (by fun_prop)
  exact fun x => scalar_denominator_ne_zero x e he

theorem scalarKernel_integrable (e : ℝ) (he : |e| ≤ 3/4) : Integrable (fun x => scalarKernel x e) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 4)
    (scalarKernel_continuous e he).aestronglyMeasurable
  filter_upwards [] with x
  simpa [div_eq_mul_inv] using scalarKernel_bound x e he

theorem profileIntegrand_bound (a b e f g t : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    ‖profileIntegrand a b e f g t‖ ≤ 64 / (1+t^2) := by
  have hb (x h : ℝ) (hh : |h| ≤ 3/4) : ‖scalarKernel x h‖ ≤ 4 := by
    have hp := scalarKernel_bound x h hh
    have hq : 4 / (1+x^2) ≤ 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg x]
    exact hp.trans hq
  have h₁ := hb (t-a) e he
  have h₂ := hb (t-b) f hf
  have h₃ := scalarKernel_bound t (-g) (by simpa using hg)
  unfold profileIntegrand
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (4*4) * (4/(1+t^2)) := mul_le_mul
      (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)) h₃ (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem profileIntegrand_integrable (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    Integrable (profileIntegrand a b e f g) := by
  have hc : Continuous (profileIntegrand a b e f g) := by
    exact (((scalarKernel_continuous e he).comp (continuous_id.sub continuous_const)).mul
      ((scalarKernel_continuous f hf).comp (continuous_id.sub continuous_const))).mul
        (scalarKernel_continuous (-g) (by simpa using hg))
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul 64) hc.aestronglyMeasurable
  filter_upwards [] with t
  simpa [div_eq_mul_inv] using profileIntegrand_bound a b e f g t he hf hg

end
end HigherCorrelations
