import HigherCorrelations.PairMeanKernelTail

/-! UNCONDITIONAL integrability, mass, and bandwidth of the explicit
interval envelopes. Pointwise sandwiching is proved separately. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex Set
open scoped FourierTransform Convolution

theorem pairMeanInterval_nonneg (T t : ℝ) : 0 ≤ pairMeanInterval T t := by
  classical
  unfold pairMeanInterval
  by_cases h : t ∈ Icc 0 T <;> simp [h]

theorem pairMeanInterval_le_one (T t : ℝ) : pairMeanInterval T t ≤ 1 := by
  classical
  unfold pairMeanInterval
  by_cases h : t ∈ Icc 0 T <;> simp [h]

theorem pairMeanInterval_measurable (T : ℝ) : Measurable (pairMeanInterval T) :=
  measurable_const.indicator measurableSet_Icc

theorem pairMeanInterval_integrable (T : ℝ) : Integrable (pairMeanInterval T) :=
  (integrable_indicator_iff measurableSet_Icc).mpr
    (show IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc 0 T) from continuous_const.integrableOn_Icc)

theorem pairMeanInterval_mass (T : ℝ) (hT : 0 ≤ T) : (∫ t, pairMeanInterval T t) = T := by
  simp [pairMeanInterval, Real.volume_real_Icc, max_eq_left hT]

theorem pairMeanScaledK_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (pairMeanScaledK δ) :=
  (pairMeanK_integrable.comp_mul_left' hδ.ne').const_mul δ

theorem pairMeanScaledK_nonneg (δ t : ℝ) (hδ : 0 ≤ δ) : 0 ≤ pairMeanScaledK δ t :=
  mul_nonneg hδ (pairMeanK_nonneg _)

theorem pairMeanScaledK_mass (δ : ℝ) (hδ : 0 < δ) : (∫ t, pairMeanScaledK δ t) = 1 := by
  unfold pairMeanScaledK
  rw [integral_const_mul, Measure.integral_comp_mul_left, pairMeanK_mass]
  simp [abs_of_pos (inv_pos.mpr hδ), hδ.ne']

theorem pairMeanEnvelope_integrable (T δ ε : ℝ) (hδ : 0 < δ) :
    Integrable (pairMeanEnvelope T δ ε) := by
  have hB := pairMeanB_integrable.comp_mul_left' hδ.ne'
  exact (pairMeanConvolution_integrable _ _ (pairMeanInterval_integrable T)
    (pairMeanScaledK_integrable δ hδ)).add ((hB.add (hB.comp_sub_right T)).const_mul _)

theorem pairMeanEnvelope_mass (T δ ε : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) :
    (∫ t, pairMeanEnvelope T δ ε t) = T+ε*512/δ := by
  have hB := pairMeanB_integrable.comp_mul_left' hδ.ne'
  have hcorr : Integrable (fun t => ε*64*(pairMeanB (δ*t)+pairMeanB (δ*(t-T)))) :=
    (hB.add (hB.comp_sub_right T)).const_mul (ε*64)
  unfold pairMeanEnvelope
  rw [integral_add (pairMeanConvolution_integrable _ _ (pairMeanInterval_integrable T)
    (pairMeanScaledK_integrable δ hδ)) hcorr,
    integral_const_mul, integral_add hB (hB.comp_sub_right T)]
  have hc : (∫ t, pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t) = T := by
    have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (pairMeanInterval_integrable T) (pairMeanScaledK_integrable δ hδ)
    change (∫ t, pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t) =
      (∫ t, pairMeanInterval T t)*(∫ t, pairMeanScaledK δ t) at h
    simpa only [pairMeanInterval_mass T hT,pairMeanScaledK_mass δ hδ,mul_one] using h
  rw [hc, integral_sub_right_eq_self (μ := volume) (fun t => pairMeanB (δ*t)) T,
    Measure.integral_comp_mul_left, pairMeanB_mass]
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hδ)]
  ring

theorem pairMeanEnvelope_norm_bound (T δ ε : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hε : |ε| ≤ 1) : (∫ t, ‖pairMeanEnvelope T δ ε t‖) ≤ T+512/δ := by
  have hle (t : ℝ) : ‖pairMeanEnvelope T δ ε t‖ ≤ pairMeanEnvelope T δ 1 t := by
    have hc : 0 ≤ pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t :=
      integral_nonneg fun u => mul_nonneg (pairMeanInterval_nonneg _ _) (pairMeanScaledK_nonneg _ _ hδ.le)
    have hb : 0 ≤ pairMeanB (δ*t)+pairMeanB (δ*(t-T)) := add_nonneg (pairMeanB_nonneg _) (pairMeanB_nonneg _)
    unfold pairMeanEnvelope
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t| +
          |ε*64*(pairMeanB (δ*t)+pairMeanB (δ*(t-T)))| := abs_add_le _ _
      _ ≤ pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t+
          1*64*(pairMeanB (δ*t)+pairMeanB (δ*(t-T))) := by
        rw [abs_of_nonneg hc,abs_mul,abs_mul,abs_of_nonneg hb]
        norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 64)]
        gcongr
        linarith
  have h := integral_mono (pairMeanEnvelope_integrable T δ ε hδ).norm
    (pairMeanEnvelope_integrable T δ 1 hδ) hle
  simpa only [pairMeanEnvelope_mass T δ 1 hT hδ,one_mul] using h

theorem pairMeanEnvelope_fourier_zero (T δ ε ξ : ℝ) (hδ : 0 < δ) (hξ : δ ≤ |ξ|) :
    pairMeanFourier (fun t => (pairMeanEnvelope T δ ε t:ℂ)) ξ = 0 := by
  have hK : pairMeanFourier (fun t => (pairMeanScaledK δ t:ℂ)) ξ = 0 := by
    have he : (fun t => (pairMeanScaledK δ t:ℂ)) = fun t => (δ:ℂ)*(pairMeanK (δ*t):ℂ) := by
      funext t
      simp [pairMeanScaledK]
    rw [he,pairMeanFourier_const_mul,pairMeanFourier_mul (fun t => (pairMeanK t:ℂ)) _ _ hδ.ne',pairMeanK_fourier_zero]
    · simp
    · rw [abs_div,abs_of_pos hδ]
      exact (le_div_iff₀ hδ).mpr (by simpa using hξ)
  have hB : pairMeanFourier (fun t => (pairMeanB (δ*t):ℂ)) ξ = 0 := by
    rw [pairMeanFourier_mul (fun t => (pairMeanB t:ℂ)) _ _ hδ.ne',pairMeanB_fourier_zero]
    · simp
    · rw [abs_div,abs_of_pos hδ]
      apply (le_div_iff₀ hδ).mpr
      linarith
  have hi := pairMeanInterval_integrable T
  have hk := pairMeanScaledK_integrable δ hδ
  have hb := pairMeanB_integrable.comp_mul_left' hδ.ne'
  have hc := pairMeanConvolution_integrable _ _ hi hk
  have he : (fun t => (pairMeanEnvelope T δ ε t:ℂ)) = fun t =>
      (pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t:ℂ) +
        (ε:ℂ)*64*((pairMeanB (δ*t):ℂ)+(pairMeanB (δ*(t-T)):ℂ)) := by
    funext t
    simp only [pairMeanEnvelope]
    push_cast
    rfl
  have hcorr : Integrable (fun t => (ε:ℂ)*64*((pairMeanB (δ*t):ℂ)+(pairMeanB (δ*(t-T)):ℂ))) :=
    ((hb.ofReal).add ((hb.comp_sub_right T).ofReal)).const_mul ((ε:ℂ)*64)
  rw [he, pairMeanFourier_add _ _ (show Integrable (fun t => (pairMeanConvolution (pairMeanInterval T) (pairMeanScaledK δ) t:ℂ)) from hc.ofReal) hcorr ξ,
    pairMeanFourier_const_mul, pairMeanFourier_add _ _ (show Integrable (fun t => (pairMeanB (δ*t):ℂ)) from hb.ofReal)
      (show Integrable (fun t => (pairMeanB (δ*(t-T)):ℂ)) from (hb.comp_sub_right T).ofReal) ξ,
    pairMeanFourier_sub (fun t => (pairMeanB (δ*t):ℂ)) T ξ,hB]
  simp only [mul_zero,add_zero]
  have hec := funext (pairMeanConvolution_complex (pairMeanInterval T) (pairMeanScaledK δ))
  rw [hec,pairMeanFourier_eq,Real.fourier_mul_convolution_eq
    (show Integrable (fun t => (pairMeanInterval T t:ℂ)) from hi.ofReal)
    (show Integrable (fun t => (pairMeanScaledK δ t:ℂ)) from hk.ofReal),
    ← pairMeanFourier_eq, ← pairMeanFourier_eq,hK,mul_zero]

end
end HigherCorrelations
