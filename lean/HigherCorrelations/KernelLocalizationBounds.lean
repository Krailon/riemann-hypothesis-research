import HigherCorrelations.KernelLocalizationIdentity
import HigherCorrelations.PairKernelIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-! UNCONDITIONAL fixed-tuple localization bounds. The half-strip bound is
uniform through its endpoints. No sum over zero occurrences is taken. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem scalar_denominator_half_strip (x e : ℝ) (he : |e| ≤ 1/2) :
    (3/4:ℝ)*(1+x^2) ≤ ‖1+((x:ℂ)+Complex.I*e)^2‖ := by
  have h := Complex.re_le_norm (1+((x:ℂ)+Complex.I*e)^2)
  have hr : (1+((x:ℂ)+Complex.I*e)^2).re = 1+x^2-e^2 := by
    simp [pow_two, Complex.mul_re]; ring
  rw [hr] at h
  rcases abs_le.mp he with ⟨hl,hu⟩
  nlinarith [sq_nonneg x]

theorem scalarKernel_half_strip_bound (x e : ℝ) (he : |e| ≤ 1/2) :
    ‖scalarKernel x e‖ ≤ (4/3:ℝ)/(1+x^2) := by
  have hb := scalar_denominator_half_strip x e he
  have hn : 0 < ‖1+((x:ℂ)+Complex.I*e)^2‖ := by nlinarith [sq_nonneg x]
  rw [scalarKernel, norm_inv, inv_eq_one_div]
  apply (div_le_div_iff₀ hn (by positivity : 0 < 1+x^2)).mpr
  nlinarith

private theorem pair_real_translate (a b u : ℝ) :
    pairKernelProduct (a-b) 0 0 (u-b) =
      ((1/((1+(u-a)^2)*(1+(u-b)^2)):ℝ):ℂ) := by
  unfold pairKernelProduct scalarKernel
  push_cast
  simp only [mul_zero, add_zero, one_div, mul_inv_rev]
  ring

theorem localization_pair_majorant_integrable (a b : ℝ) :
    Integrable (fun u : ℝ => 1/((1+(u-a)^2)*(1+(u-b)^2))) := by
  have h := ((pairKernelProduct_integrable (a-b) 0 0 (by norm_num) (by norm_num)).comp_sub_right b).re
  change Integrable (fun u => (pairKernelProduct (a-b) 0 0 (u-b)).re) at h
  simpa only [pair_real_translate, Complex.ofReal_re] using h

theorem localization_pair_majorant_integral (a b : ℝ) :
    (∫ u : ℝ, 1/((1+(u-a)^2)*(1+(u-b)^2))) =
      2*Real.pi/(4+(a-b)^2) := by
  have h := pairKernelIntegral_eq (a-b) 0 0 (by norm_num) (by norm_num)
  rw [pairKernelIntegral,
    ← integral_sub_right_eq_self (pairKernelProduct (a-b) 0 0) b] at h
  simp_rw [pair_real_translate] at h
  rw [integral_complex_ofReal] at h
  have hv : pairKernelValue (a-b) 0 0 = ((2*Real.pi/(4+(a-b)^2):ℝ):ℂ) := by
    unfold pairKernelValue
    push_cast
    simp
  rw [hv] at h
  exact Complex.ofReal_injective h

theorem localization_anchor_moment_bound (u : ℝ) :
    |u|/(1+u^2) ≤ (1/2:ℝ) := by
  apply (div_le_iff₀ (by positivity : 0 < 1+u^2)).mpr
  nlinarith [sq_nonneg (|u|-1), sq_abs u]

theorem profileIntegrand_localization_moment (a b e f g u : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) (hg : |g| ≤ 1/2) :
    |u| *‖profileIntegrand a b e f g u‖ ≤
      (32/27:ℝ)*(1/((1+(u-a)^2)*(1+(u-b)^2))) := by
  have h₁ := scalarKernel_half_strip_bound (u-a) e he
  have h₂ := scalarKernel_half_strip_bound (u-b) f hf
  have h₃ := scalarKernel_half_strip_bound u (-g) (by simpa using hg)
  have hh := mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
  have hhh := mul_le_mul hh h₃ (norm_nonneg _) (by positivity)
  have hm := localization_anchor_moment_bound u
  rw [profileIntegrand, norm_mul, norm_mul]
  calc
    _ ≤ |u| *(((4/3)/(1+(u-a)^2))*((4/3)/(1+(u-b)^2))*((4/3)/(1+u^2))) :=
      mul_le_mul_of_nonneg_left hhh (abs_nonneg _)
    _ = (64/27:ℝ)*(|u|/(1+u^2))*(1/((1+(u-a)^2)*(1+(u-b)^2))) := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (64/27:ℝ)*(1/2)*(1/((1+(u-a)^2)*(1+(u-b)^2))) := by gcongr
    _ = _ := by ring

theorem localization_weight_difference (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T c u : ℝ) (hT : 0<T) :
    |ω ((c+u)/T)-ω (c/T)| ≤ (M:ℝ)/T*|u| := by
  have h := hω.dist_le_mul ((c+u)/T) (c/T)
  rw [Real.dist_eq, Real.dist_eq] at h
  have he : (c+u)/T-c/T=u/T := by ring
  rw [he, abs_div, abs_of_pos hT] at h
  convert h using 1
  ring

theorem tripleKernelLocalizationIntegrand_bound (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) (u : ℝ) :
    ‖tripleKernelLocalizationIntegrand ω T v u‖ ≤
      (32*(M:ℝ)/(27*T))*(1/((1+(u-(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2)))^2)*
        (1+(u-(occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2)))^2))) := by
  have hm := profileIntegrand_localization_moment
    (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))
    (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))
    (occurrenceDisplacement (v 0)) (occurrenceDisplacement (v 1))
    (occurrenceDisplacement (v 2)) u
    (occurrence_displacement_lt (v 0)).le (occurrence_displacement_lt (v 1)).le
    (occurrence_displacement_lt (v 2)).le
  change |u| *‖tripleAnchoredProfileIntegrand v u‖ ≤ _ at hm
  rw [tripleKernelLocalizationIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ((M:ℝ)/T*|u|)*‖tripleAnchoredProfileIntegrand v u‖ :=
      mul_le_mul_of_nonneg_right (localization_weight_difference ω M hω T _ u hT) (norm_nonneg _)
    _ = ((M:ℝ)/T)*(|u| *‖tripleAnchoredProfileIntegrand v u‖) := by ring
    _ ≤ ((M:ℝ)/T)*_ := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem tripleKernelLocalizationIntegrand_integrable_lipschitz (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (tripleKernelLocalizationIntegrand ω T v) := by
  have hi := (localization_pair_majorant_integrable
    (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))
    (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))).const_mul (32*(M:ℝ)/(27*T))
  apply Integrable.mono' hi
  · unfold tripleKernelLocalizationIntegrand tripleAnchoredProfileIntegrand profileIntegrand
    have hk (i : Fin 3) := scalarKernel_continuous (occurrenceDisplacement (v i))
      (le_trans (occurrence_displacement_lt (v i)).le (by norm_num))
    have ha := scalarKernel_continuous (-occurrenceDisplacement (v 2))
      (by simpa using le_trans (occurrence_displacement_lt (v 2)).le (by norm_num : (1/2:ℝ) ≤ 3/4))
    exact ((Complex.continuous_ofReal.comp ((hω.continuous.comp
      ((continuous_const.add continuous_id).div_const T)).sub continuous_const)).mul
      (((hk 0).comp (continuous_id.sub continuous_const)).mul
        ((hk 1).comp (continuous_id.sub continuous_const)) |>.mul ha)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (tripleKernelLocalizationIntegrand_bound ω M hω T hT v)

theorem tripleKernelLocalizationError_bound (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤
      64*Real.pi*(M:ℝ)/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by
  have hi := (localization_pair_majorant_integrable
    (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))
    (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))).const_mul (32*(M:ℝ)/(27*T))
  have hb := norm_integral_le_of_norm_le hi
    (Filter.Eventually.of_forall (tripleKernelLocalizationIntegrand_bound ω M hω T hT v))
  rw [integral_const_mul, localization_pair_majorant_integral] at hb
  rw [tripleKernelLocalizationError, norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ (1/T)*_ := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      have he : (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))-
        (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2)) =
        occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1) := by ring
      rw [he]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem tripleKernelLocalizationError_bound_deriv (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hd : ∀ x, |deriv ω x|≤M)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by
  apply tripleKernelLocalizationError_bound ω ⟨M,hM⟩ _ T hT v
  exact lipschitzWith_of_nnnorm_deriv_le hω (fun x => by
    change ‖deriv ω x‖ ≤ M
    simpa only [Real.norm_eq_abs] using hd x)


end
end HigherCorrelations
