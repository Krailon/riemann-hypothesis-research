import HigherCorrelations.MainTermComparisonDefinitions
import HigherCorrelations.SineBenchmarkAssembly
import HigherCorrelations.ComplexFourierRegularity
import HigherCorrelations.SignedTrace

/-! UNCONDITIONAL exact benchmark comparison, including the deterministic boundary. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem mainTermFrequencyTest_apply (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x : FourierPlane) :
    mainTermFrequencyTest φ hφ hc x = φ (planeCoords x) := rfl

theorem mainTermPhysicalTest_apply (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x : FourierPlane) :
    mainTermPhysicalTest φ hφ hc x =
      complexFourier φ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ)) := by
  rw [mainTermPhysicalTest,SchwartzMap.fourierInv_coe,complexFourier_real_eq_inverse]
  rfl

theorem mainTermPhysicalTest_fourier (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    𝓕 (mainTermPhysicalTest φ hφ hc) = mainTermFrequencyTest φ hφ hc := by
  exact FourierTransform.fourier_fourierInv_eq _

theorem sineR2_reflection (r : ℝ) : sineR2 (-r) = sineR2 r := by
  simp [sineR2,pairMeanSinc,Real.sinc_neg,mul_neg]

theorem sineR3_reflection (p : ℝ × ℝ) : sineR3 (-p) = sineR3 p := by
  simp [sineR3,pairMeanSinc,mul_neg,neg_sub_neg,sineCycle_reflection,Real.sinc_neg]
  have h : Real.sinc (Real.pi*(p.2-p.1)) = Real.sinc (Real.pi*(p.1-p.2)) := by
    rw [show p.2-p.1 = -(p.1-p.2) by ring,mul_neg,Real.sinc_neg]
  rw [show -p.1+p.2 = p.2-p.1 by ring,h]

theorem sineBenchmark_reflection (F G : 𝓢(FourierPlane,ℂ))
    (hG : ∀ x, G x = F (-x)) : sineBenchmark G = sineBenchmark F := by
  have hp : sinePlanePair (fun p => sineR3 (planeCoords p)) G =
      sinePlanePair (fun p => sineR3 (planeCoords p)) F := by
    have hh := integral_neg_eq_self (fun p : FourierPlane => F p*sineR3 (planeCoords p)) volume
    simpa only [sinePlanePair,hG,map_neg,sineR3_reflection] using hh
  have hl (j : Fin 3) : sineLinePair j sineR2 G = sineLinePair j sineR2 F := by
    have hh := integral_neg_eq_self (fun r : ℝ => F (sineLine j r)*sineR2 r) volume
    simpa only [sineLinePair,hG,sineLine,map_neg,sineR2_reflection] using hh
  rw [sineBenchmark_five,sineBenchmark_five,hp]
  simp only [hl,hG,neg_zero]

theorem sineBenchmark_inverse_pairing (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark (𝓕⁻ F) = sineBenchmarkSpectrum F := by
  rw [← sineBenchmark_fourier]
  apply sineBenchmark_reflection
  intro x
  rw [SchwartzMap.fourierInv_apply_eq]
  rfl

end
end HigherCorrelations
