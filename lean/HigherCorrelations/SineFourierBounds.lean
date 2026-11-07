import HigherCorrelations.SineFourierDefinitions
import HigherCorrelations.SineOverlap
import HigherCorrelations.PairMeanTriangle
import HigherCorrelations.ComplexFourierDecay

/-! UNCONDITIONAL boundedness and compact majorants for the sinc pairing. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap

theorem sineCycle_continuous : Continuous sineCycle := by
  exact ((Complex.continuous_ofReal.comp (pairMeanSinc_continuous.comp continuous_fst)).mul
    (Complex.continuous_ofReal.comp (pairMeanSinc_continuous.comp continuous_snd))).mul
    (Complex.continuous_ofReal.comp (pairMeanSinc_continuous.comp (continuous_fst.sub continuous_snd)))

theorem sineCycle_bound (p : ℝ × ℝ) : ‖sineCycle p‖ ≤ 1 := by
  simp only [sineCycle,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h1 := pairMeanSinc_abs_le_one p.1
  have h2 := pairMeanSinc_abs_le_one p.2
  have h3 := pairMeanSinc_abs_le_one (p.1-p.2)
  calc
    _ ≤ 1*1*1 := mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num))
      h3 (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem sineCycle_reflection (p : ℝ × ℝ) : sineCycle (-p) = sineCycle p := by
  simp only [sineCycle,Prod.fst_neg,Prod.snd_neg,neg_sub_neg]
  rw [pairMeanSinc_even,pairMeanSinc_even,← neg_sub p.1 p.2,pairMeanSinc_even]

theorem sineCycle_origin : sineCycle (0,0) = 1 := by simp [sineCycle,pairMeanSinc_zero]

theorem sineCycle_axes (r : ℝ) :
    sineCycle (r,0) = (pairMeanSinc r:ℂ)^2 ∧
    sineCycle (0,r) = (pairMeanSinc r:ℂ)^2 ∧
    sineCycle (r,r) = (pairMeanSinc r:ℂ)^2 := by
  simp [sineCycle,pairMeanSinc_zero,pairMeanSinc_even,pow_two]

theorem sineCycleDensity_bounds (ξ η : ℝ) : 0 ≤ sineCycleDensity ξ η ∧ sineCycleDensity ξ η ≤ 1 := by
  have h := signedGauge_nonneg (ξ,η)
  simp only [sineCycleDensity]
  exact ⟨le_max_left _ _,max_le (by norm_num) (by linarith)⟩

theorem sineCycleDensity_reflection (ξ η : ℝ) : sineCycleDensity (-ξ) (-η) = sineCycleDensity ξ η := by
  simp only [sineCycleDensity,signedGauge,abs_neg,← neg_add]

theorem sineCycleDensity_continuous : Continuous (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) := by
  exact continuous_const.max (continuous_const.sub signedGauge_continuous)

theorem sineCycleDensity_compactSupport : HasCompactSupport (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1))
  intro p hp
  have h : 1 ≤ signedGauge p := by
    by_contra hn
    have hg : signedGauge p < 1 := lt_of_not_ge hn
    have hx : |p.1| < 1 := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hg
    have hy : |p.2| < 1 := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hg
    exact hp ⟨⟨(abs_lt.mp hx).1.le,(abs_lt.mp hx).2.le⟩,
      ⟨(abs_lt.mp hy).1.le,(abs_lt.mp hy).2.le⟩⟩
  exact max_eq_left (sub_nonpos.mpr h)

theorem sineCycleDensity_integrable : Integrable (fun p : ℝ × ℝ => sineCycleDensity p.1 p.2) :=
  sineCycleDensity_continuous.integrable_of_hasCompactSupport sineCycleDensity_compactSupport

theorem sineDensityPlane_integrable : Integrable sineDensityPlane := by
  exact (WithLp.volume_preserving_ofLp ℝ ℝ).integrable_comp_emb
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph.measurableEmbedding |>.mpr
    sineCycleDensity_integrable.ofReal

theorem sineCyclePlane_weighted_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun x => F x*sineCyclePlane x) := by
  apply (F.integrable (μ := volume)).norm.mono'
    ((F.continuous.mul (sineCycle_continuous.comp planeCoords.continuous)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [sineCyclePlane,Pi.mul_apply,Function.comp_apply,norm_mul,mul_one] using
      mul_le_mul_of_nonneg_left (sineCycle_bound (planeCoords x)) (norm_nonneg (F x))

theorem sineDensityPlane_weighted_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun x => F x*sineDensityPlane x) := by
  apply (F.integrable (μ := volume)).norm.mono'
    ((F.continuous.mul (Complex.continuous_ofReal.comp
      (sineCycleDensity_continuous.comp planeCoords.continuous))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    have h := sineCycleDensity_bounds (planeCoords x).1 (planeCoords x).2
    simpa only [sineDensityPlane,Pi.mul_apply,Function.comp_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg h.1,mul_one] using mul_le_mul_of_nonneg_left h.2 (norm_nonneg (F x))

end
end HigherCorrelations
