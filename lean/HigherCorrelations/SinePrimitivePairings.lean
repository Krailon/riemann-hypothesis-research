import HigherCorrelations.SineFourierSlice
import HigherCorrelations.SineLineDuality
import HigherCorrelations.SineBenchmarkIntegrability

/-! UNCONDITIONAL primitive Fourier rows used in the benchmark assembly. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem sineFourier_twice (F : 𝓢(FourierPlane,ℂ)) (x : FourierPlane) :
    (𝓕 (𝓕 F)) x = F (-x) := by
  have hi : (𝓕⁻ (𝓕 F) : 𝓢(FourierPlane,ℂ)) = F := FourierTransform.fourierInv_fourier_eq F
  have h := congrArg (fun G : 𝓢(FourierPlane,ℂ) => G (-x)) hi
  rw [SchwartzMap.fourierInv_apply_eq] at h
  change (𝓕 (𝓕 F)) (-(-x)) = F (-x) at h
  simpa only [neg_neg] using h

theorem sineDirection_triangle_reflection (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r, F (-sineDirection a b r)*(pairMeanTriangle r:ℂ)) =
      ∫ r, F (sineDirection a b r)*(pairMeanTriangle r:ℂ) := by
  have h := integral_neg_eq_self (fun r : ℝ => F (sineDirection a b r)*(pairMeanTriangle r:ℂ)) volume
  simpa [sineDirection,map_neg,pairMeanTriangle,abs_neg] using h

theorem sineDirection_plane_square_pairing (a b : ℝ) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ p, (𝓕 F) p*(pairMeanSinc (sineDirectionForm a b p):ℂ)^2) =
      ∫ r, F (sineDirection a b r)*(pairMeanTriangle r:ℂ) := by
  have h := sineDirection_triangle_pairing a b (𝓕 F)
  simp_rw [sineFourier_twice] at h
  rw [sineDirection_triangle_reflection] at h
  exact h.symm

theorem sineLine_square_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j (fun r => (pairMeanSinc r:ℂ)^2) (𝓕 F) =
      sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F := by
  fin_cases j
  · simpa [sineLinePair,sinePlanePair,sineLine,sineLineCoords,sineLineForm,sineDirection,
      sineDirectionCLM,sineDirectionForm] using sineDirection_square_pairing 1 0 F
  · simpa [sineLinePair,sinePlanePair,sineLine,sineLineCoords,sineLineForm,sineDirection,
      sineDirectionCLM,sineDirectionForm] using sineDirection_square_pairing 0 1 F
  · simpa [sineLinePair,sinePlanePair,sineLine,sineLineCoords,sineLineForm,sineDirection,
      sineDirectionCLM,sineDirectionForm] using sineDirection_square_pairing 1 1 F

theorem sinePlane_square_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2) (𝓕 F) =
      sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F := by
  fin_cases j
  · simpa [sineComplementPair,sinePlanePair,sineComplement,sineSliceMap,sineDifferenceForm,sineDirection,
      sineDirectionCLM,sineDirectionForm] using sineDirection_plane_square_pairing 0 1 F
  · simpa [sineComplementPair,sinePlanePair,sineComplement,sineSliceMap,sineDifferenceForm,sineDirection,
      sineDirectionCLM,sineDirectionForm] using sineDirection_plane_square_pairing 1 0 F
  · simpa [sineComplementPair,sinePlanePair,sineComplement,sineSliceMap,sineDifferenceForm,sineDirection,
      sineDirectionCLM,sineDirectionForm,sub_eq_add_neg] using sineDirection_plane_square_pairing 1 (-1) F

theorem sineLine_constant_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j (fun _ => 1) (𝓕 F) = sineComplementPair j (fun _ => 1) F := by
  simpa only [sineLinePair,sineComplementPair,mul_one] using sineLine_fourier_integral j F

theorem sinePlane_constant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun _ => 1) (𝓕 F) = F 0 := by
  have hi : (𝓕⁻ (𝓕 F) : 𝓢(FourierPlane,ℂ)) = F := FourierTransform.fourierInv_fourier_eq F
  have h := congrArg (fun G : 𝓢(FourierPlane,ℂ) => G 0) hi
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at h
  simpa [sinePlanePair] using h

theorem sineAtom_fourier (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 F) 0 = sinePlanePair (fun _ => 1) F := by
  simp [SchwartzMap.fourier_coe,Real.fourier_eq,sinePlanePair]

theorem sineCycle_distribution_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair sineCyclePlane (𝓕 F) = sinePlanePair sineDensityPlane F := by
  have h := sineCycle_pairing (𝓕 F)
  simp_rw [sineFourier_twice] at h
  have hr := integral_neg_eq_self (fun p : FourierPlane => F p*sineDensityPlane p) volume
  have he (p : FourierPlane) : sineDensityPlane (-p) = sineDensityPlane p := by
    simp [sineDensityPlane,map_neg,sineCycleDensity_reflection]
  simp_rw [he] at hr
  exact h.trans hr

end
end HigherCorrelations
