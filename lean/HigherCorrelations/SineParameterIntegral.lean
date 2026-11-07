import HigherCorrelations.SineFourierBounds
import Mathlib.MeasureTheory.Integral.Prod

/-! UNCONDITIONAL compact parameter majorant and justified Fubini for the cycle. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory

private theorem box_measurable : Measurable pairMeanBox :=
  measurable_const.indicator measurableSet_Icc

private theorem box_norm (t : ℝ) : ‖pairMeanBox t‖ ≤ 1 := by
  classical
  unfold pairMeanBox
  by_cases h : t ∈ Icc (-(1/2:ℝ)) (1/2)
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

theorem sineParameterIntegrand_majorant (u v : ℝ) (q : ℝ × (ℝ × ℝ)) :
    ‖sineParameterIntegrand u v q‖ ≤
      (sineInterval ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)).indicator (fun _ => (1:ℝ)) q := by
  classical
  by_cases h0 : q.1 ∈ sineInterval
  · by_cases h1 : q.2.1-q.1 ∈ sineInterval
    · by_cases h2 : q.2.2+q.1 ∈ sineInterval
      · have hq : q ∈ sineInterval ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) := by
          simp only [sineInterval,mem_Icc] at h0 h1 h2
          exact ⟨h0,⟨by constructor <;> linarith [h0.1,h0.2,h1.1,h1.2],
            by constructor <;> linarith [h0.1,h0.2,h2.1,h2.2]⟩⟩
        rw [indicator_of_mem hq]
        simp only [sineParameterIntegrand,norm_mul,pairMeanCharacter_norm,mul_one]
        nlinarith [box_norm q.1,box_norm (q.2.1-q.1),box_norm (q.2.2+q.1),
          norm_nonneg (pairMeanBox q.1),norm_nonneg (pairMeanBox (q.2.1-q.1)),
          norm_nonneg (pairMeanBox (q.2.2+q.1)),
          mul_le_mul (box_norm q.1) (box_norm (q.2.1-q.1)) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)]
      · have hz : pairMeanBox (q.2.2+q.1) = 0 := indicator_of_notMem h2 _
        simp only [sineParameterIntegrand,hz,mul_zero,zero_mul,norm_zero]
        exact indicator_nonneg (fun _ _ => by norm_num) _
    · have hz : pairMeanBox (q.2.1-q.1) = 0 := indicator_of_notMem h1 _
      simp only [sineParameterIntegrand,hz,mul_zero,zero_mul,norm_zero]
      exact indicator_nonneg (fun _ _ => by norm_num) _
  · have hz : pairMeanBox q.1 = 0 := indicator_of_notMem h0 _
    simp only [sineParameterIntegrand,hz,zero_mul,norm_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) _

theorem sineParameterIntegrand_integrable (u v : ℝ) : Integrable (sineParameterIntegrand u v) := by
  have hm : Measurable (sineParameterIntegrand u v) := by
    exact (((box_measurable.comp measurable_fst).mul
      (box_measurable.comp (measurable_fst.comp measurable_snd |>.sub measurable_fst))).mul
      (box_measurable.comp (measurable_snd.comp measurable_snd |>.add measurable_fst))).mul
      (pairMeanCharacter_continuous.measurable.comp (by fun_prop))
  have hk : IsCompact (sineInterval ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hi : Integrable ((sineInterval ×ˢ (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)).indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff hk.measurableSet).mpr (integrableOn_const hk.measure_lt_top.ne)
  exact hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (sineParameterIntegrand_majorant u v))

theorem sineParameterIntegrand_fubini (u v : ℝ) :
    (∫ p : ℝ × ℝ, ∫ d : ℝ, sineParameterIntegrand u v (d,p)) =
      ∫ d : ℝ, ∫ p : ℝ × ℝ, sineParameterIntegrand u v (d,p) := by
  have hi : Integrable (Function.uncurry (fun (d : ℝ) (p : ℝ × ℝ) =>
      sineParameterIntegrand u v (d,p))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact sineParameterIntegrand_integrable u v
  exact (integral_integral_swap hi).symm

theorem sineParameterIntegrand_inner (u v : ℝ) (p : ℝ × ℝ) :
    (∫ d : ℝ, sineParameterIntegrand u v (d,p)) =
      (sineCycleDensity p.1 p.2 : ℂ) * pairMeanCharacter (u*p.1+v*p.2) := by
  have box_cast (t : ℝ) : pairMeanBox t = Complex.ofReal (sineInterval.indicator (fun _ => (1:ℝ)) t) := by
    classical
    change sineInterval.indicator (fun _ => (1:ℂ)) t = _
    by_cases h : t ∈ sineInterval
    · simp only [indicator_of_mem h,Complex.ofReal_one]
    · simp only [indicator_of_notMem h,Complex.ofReal_zero]
  have he (d : ℝ) : sineParameterIntegrand u v (d,p) =
      (sineOverlapIntegrand p.1 p.2 d : ℂ) * pairMeanCharacter (u*p.1+v*p.2) := by
    simp only [sineParameterIntegrand,sineOverlapIntegrand,box_cast,Complex.ofReal_mul]
  simp_rw [he]
  rw [integral_mul_const,integral_complex_ofReal,sineOverlap_integral]

end
end HigherCorrelations
