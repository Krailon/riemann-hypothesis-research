import HigherCorrelations.SineFourierTransform

/-! UNCONDITIONAL bilinear Schwartz pairings in the negative-forward 2pi convention.
No conjugation or support restriction is imposed on the complex Schwartz test. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem sineCycle_pairing (F : 𝓢(FourierPlane,ℂ)) :
    (∫ x, F x*sineCyclePlane x) = ∫ ξ, (𝓕 F) ξ*sineDensityPlane ξ := by
  have he : (innerₗ FourierPlane).flip = innerₗ FourierPlane := by
    ext x y
    simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ FourierPlane) Real.continuous_fourierChar continuous_inner
    sineDensityPlane_integrable (F.integrable (μ := volume))
  rw [he] at h
  change (∫ x, (𝓕 sineDensityPlane) x*F x) =
    ∫ ξ, sineDensityPlane ξ*(𝓕 (F : FourierPlane → ℂ)) ξ at h
  simpa only [sineDensityPlane_fourier,SchwartzMap.fourier_coe,mul_comm] using h

theorem sineCycle_inverse_pairing (φ : 𝓢(FourierPlane,ℂ)) :
    (∫ x, (𝓕⁻ φ) x*sineCyclePlane x) = ∫ ξ, φ ξ*sineDensityPlane ξ := by
  simpa only [FourierTransform.fourier_fourierInv_eq] using sineCycle_pairing (𝓕⁻ φ)

theorem sineSquared_weighted_integrable (F : 𝓢(ℝ,ℂ)) :
    Integrable (fun x => F x*(pairMeanSinc x:ℂ)^2) := by
  apply (F.integrable (μ := volume)).norm.mono'
    ((F.continuous.mul ((Complex.continuous_ofReal.comp pairMeanSinc_continuous).pow 2)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖F x*(pairMeanSinc x:ℂ)^2‖ ≤ ‖F x‖
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have h : |pairMeanSinc x|^2 ≤ 1 := by
    simpa only [pow_two,mul_one] using
      mul_le_mul (pairMeanSinc_abs_le_one x) (pairMeanSinc_abs_le_one x)
        (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (norm_nonneg (F x))

theorem sineTriangle_weighted_integrable (F : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ => F ξ*(pairMeanTriangle ξ:ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
    (F.continuous.mul (Complex.continuous_ofReal.comp pairMeanTriangle_continuous))
  exact (pairMeanTriangle_compactSupport.comp_left rfl).mul_left

theorem sineSquared_pairing (F : 𝓢(ℝ,ℂ)) :
    (∫ x, F x*(pairMeanSinc x:ℂ)^2) = ∫ ξ, (𝓕 F) ξ*(pairMeanTriangle ξ:ℂ) := by
  have he : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext <;> simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    pairMeanTriangle_integrable.ofReal (F.integrable (μ := volume))
  rw [he] at h
  change (∫ x, (𝓕 (fun ξ => (pairMeanTriangle ξ:ℂ))) x*F x) =
    ∫ ξ, (pairMeanTriangle ξ:ℂ)*(𝓕 (F : ℝ → ℂ)) ξ at h
  have ht (x : ℝ) : (𝓕 (fun ξ => (pairMeanTriangle ξ:ℂ))) x = (pairMeanSinc x:ℂ)^2 := by
    rw [← pairMeanFourier_eq,pairMeanTriangle_fourier]
  simpa only [ht,SchwartzMap.fourier_coe,mul_comm] using h

theorem sineSquared_inverse_pairing (φ : 𝓢(ℝ,ℂ)) :
    (∫ x, (𝓕⁻ φ) x*(pairMeanSinc x:ℂ)^2) = ∫ ξ, φ ξ*(pairMeanTriangle ξ:ℂ) := by
  simpa only [FourierTransform.fourier_fourierInv_eq] using sineSquared_pairing (𝓕⁻ φ)

end
end HigherCorrelations
