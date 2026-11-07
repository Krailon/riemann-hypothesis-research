import HigherCorrelations.SineSchwartzLines

/-! UNCONDITIONAL line-plane duality for integrable weights. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

theorem sineDirection_dot (a b r : ℝ) (p : FourierPlane) :
    ⟪sineDirection a b r,p⟫ = r*sineDirectionForm a b p := by
  simp [sineDirection,sineDirectionCLM,sineDirectionForm,planeCoords,
    WithLp.prod_inner_apply,Real.inner_apply]
  ring

theorem sineDirection_fourier_duality (a b : ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*f r) =
      ∫ p, F p*pairMeanFourier f (sineDirectionForm a b p) := by
  let L : ℝ →ₗ[ℝ] FourierPlane →ₗ[ℝ] ℝ :=
    (innerₗ FourierPlane).comp (sineDirectionCLM a b).toLinearMap
  have hL : Continuous (fun p : ℝ × FourierPlane => L p.1 p.2) := by
    exact ((sineDirectionCLM a b).continuous.comp continuous_fst).inner continuous_snd
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := L) Real.continuous_fourierChar hL hf (F.integrable (μ := volume))
  have hl (p : FourierPlane) : VectorFourier.fourierIntegral Real.fourierChar volume L f p =
      pairMeanFourier f (sineDirectionForm a b p) := by
    rw [VectorFourier.fourierIntegral,pairMeanFourier]
    apply integral_congr_ae
    filter_upwards [] with r
    change Real.fourierChar (-⟪sineDirection a b r,p⟫) • f r = _
    rw [sineDirection_dot]
    simp only [Circle.smul_def,Real.fourierChar_apply,pairMeanCharacter,smul_eq_mul,
      Complex.ofReal_neg,Complex.ofReal_mul]
    congr 2
    push_cast
    ring
  have hr (r : ℝ) : VectorFourier.fourierIntegral Real.fourierChar volume L.flip (F : FourierPlane → ℂ) r =
      (𝓕 F) (sineDirection a b r) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_eq]
    unfold VectorFourier.fourierIntegral
    apply integral_congr_ae
    filter_upwards [] with p
    change Real.fourierChar (-⟪sineDirection a b r,p⟫) • F p = _
    rw [real_inner_comm]
  simpa only [hl,hr,smul_eq_mul,mul_comm] using h.symm

theorem sineDirection_square_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*(pairMeanSinc r:ℂ)^2) =
      ∫ p, F p*(pairMeanTriangle (sineDirectionForm a b p):ℂ) := by
  have hf : Integrable (fun r : ℝ => (pairMeanSinc r:ℂ)^2) := by
    convert (pairMeanSinc_sq_integrable.ofReal : Integrable (fun r : ℝ => Complex.ofReal (pairMeanSinc r^2)) volume) using 1
    funext r
    push_cast
    rfl
  have ht (t : ℝ) : pairMeanFourier (fun r => (pairMeanSinc r:ℂ)^2) t = (pairMeanTriangle t:ℂ) := by
    convert pairMeanSinc_sq_fourier t using 1
  have h := sineDirection_fourier_duality a b (fun r => (pairMeanSinc r:ℂ)^2) hf F
  simp_rw [ht] at h
  exact h

theorem sineDirection_triangle_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, (𝓕 F) (sineDirection a b r)*(pairMeanTriangle r:ℂ)) =
      ∫ p, F p*(pairMeanSinc (sineDirectionForm a b p):ℂ)^2 := by
  have h := sineDirection_fourier_duality a b (fun r => (pairMeanTriangle r:ℂ))
    pairMeanTriangle_integrable.ofReal F
  simp_rw [pairMeanTriangle_fourier] at h
  exact h

end
end HigherCorrelations
