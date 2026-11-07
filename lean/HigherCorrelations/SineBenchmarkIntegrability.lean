import HigherCorrelations.SineBenchmarkFunctionalDefinitions
import HigherCorrelations.SineSchwartzLines

/-! UNCONDITIONAL integrability and tempered realizations of bounded densities. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem sinePlane_weighted_integrable (f : FourierPlane → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ p, ‖f p‖ ≤ C) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*f p) := by
  apply (F.integrable.norm.mul_const C).mono' (F.continuous.mul hf).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖F p*f p‖ ≤ ‖F p‖*C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg _)

theorem sineLine_weighted_integrable (j : Fin 3) (w : ℝ → ℂ) (hw : Continuous w)
    (C : ℝ) (hC : ∀ r, ‖w r‖ ≤ C) (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun r => F (sineLine j r)*w r) := by
  apply ((sineLineRestriction j F).integrable.norm.mul_const C).mono'
    ((sineLineRestriction j F).continuous.mul hw).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun r => by
    change ‖F (sineLine j r)*w r‖ ≤ ‖F (sineLine j r)‖*C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)

theorem sinePlane_tempered (f : FourierPlane → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ p, ‖f p‖ ≤ C) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sinePlanePair f F := by
  let h := memLp_top_of_bound (μ := volume) hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  refine ⟨Lp.toTemperedDistribution (h.toLp f),?_⟩
  intro F
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with p hp
  simp only [hp,smul_eq_mul]

theorem sineLine_tempered (j : Fin 3) (w : ℝ → ℂ) (hw : Continuous w)
    (C : ℝ) (hC : ∀ r, ‖w r‖ ≤ C) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineLinePair j w F := by
  let h := memLp_top_of_bound (μ := volume) hw.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let A : 𝓢'(ℝ,ℂ) := Lp.toTemperedDistribution (h.toLp w)
  refine ⟨A.comp (sineLineRestriction j),?_⟩
  intro F
  change A (sineLineRestriction j F) = _
  rw [show A (sineLineRestriction j F) = (Lp.toTemperedDistribution (h.toLp w)) (sineLineRestriction j F) from rfl,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [h.coeFn_toLp] with r hr
  simp only [hr,smul_eq_mul,sineLineRestriction_apply]

theorem sineSquare_bound (r : ℝ) : ‖(pairMeanSinc r:ℂ)^2‖ ≤ 1 := by
  simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,pow_two,norm_mul,mul_one] using
    mul_le_mul (pairMeanSinc_abs_le_one r) (pairMeanSinc_abs_le_one r)
      (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem sineR2_continuous : Continuous sineR2 :=
  continuous_const.sub ((Complex.continuous_ofReal.comp pairMeanSinc_continuous).pow 2)

theorem sineR2_bound (r : ℝ) : ‖sineR2 r‖ ≤ 2 := by
  calc
    _ ≤ ‖(1:ℂ)‖+‖(pairMeanSinc r:ℂ)^2‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith [sineSquare_bound r]

theorem sineR3_continuous : Continuous (fun p : FourierPlane => sineR3 (planeCoords p)) := by
  have h1 := pairMeanSinc_continuous.comp (continuous_fst.comp planeCoords.continuous)
  have h2 := pairMeanSinc_continuous.comp (continuous_snd.comp planeCoords.continuous)
  have h3 := pairMeanSinc_continuous.comp ((continuous_fst.sub continuous_snd).comp planeCoords.continuous)
  exact (((continuous_const.sub ((Complex.continuous_ofReal.comp h1).pow 2)).sub
    ((Complex.continuous_ofReal.comp h2).pow 2)).sub ((Complex.continuous_ofReal.comp h3).pow 2)).add
    (continuous_const.mul (sineCycle_continuous.comp planeCoords.continuous))

theorem sineR3_bound (p : ℝ × ℝ) : ‖sineR3 p‖ ≤ 6 := by
  have h1 := sineSquare_bound p.1
  have h2 := sineSquare_bound p.2
  have h3 := sineSquare_bound (p.1-p.2)
  have hc := sineCycle_bound p
  have hn1 := norm_sub_le (1:ℂ) ((pairMeanSinc p.1:ℂ)^2)
  have hn2 := norm_sub_le ((1:ℂ)-(pairMeanSinc p.1:ℂ)^2) ((pairMeanSinc p.2:ℂ)^2)
  have hn3 := norm_sub_le ((1:ℂ)-(pairMeanSinc p.1:ℂ)^2-(pairMeanSinc p.2:ℂ)^2) ((pairMeanSinc (p.1-p.2):ℂ)^2)
  have hn4 := norm_add_le ((1:ℂ)-(pairMeanSinc p.1:ℂ)^2-(pairMeanSinc p.2:ℂ)^2-(pairMeanSinc (p.1-p.2):ℂ)^2) (2*sineCycle p)
  rw [norm_one] at hn1
  rw [norm_mul,show ‖(2:ℂ)‖ = 2 by norm_num] at hn4
  change ‖(1:ℂ)-(pairMeanSinc p.1:ℂ)^2-(pairMeanSinc p.2:ℂ)^2-(pairMeanSinc (p.1-p.2):ℂ)^2+2*sineCycle p‖ ≤ 6
  linarith

end
end HigherCorrelations
