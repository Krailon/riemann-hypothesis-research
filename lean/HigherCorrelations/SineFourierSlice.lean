import HigherCorrelations.SineMarginal

/-! UNCONDITIONAL constant-line Fourier slice identity, including diagonal normalization. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace

theorem sineSlice_fourier_marginal (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) (r : ℝ) :
    let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sineSliceEquiv j)
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm F)
    (𝓕 (sineMarginal G)) r = (𝓕 F) (sineLine j r) := by
  dsimp only
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sineSliceEquiv j)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm F)
  rw [← pairMeanFourier_eq,sineMarginal_fourier,SchwartzMap.fourier_coe,Real.fourier_eq']
  have hm := (WithLp.volume_preserving_ofLp ℝ ℝ).integral_comp
    planeCoords.toHomeomorph.measurableEmbedding
    (fun p : ℝ × ℝ => Complex.exp ((↑(-2*Real.pi*⟪planeCoords.symm p,sineLine j r⟫):ℂ)*Complex.I)*F (planeCoords.symm p))
  change _ = ∫ x : FourierPlane, _
  have hr : (∫ x : FourierPlane, Complex.exp ((↑(-2*Real.pi*⟪x,sineLine j r⟫):ℂ)*Complex.I) • F x) =
      ∫ p : ℝ × ℝ, Complex.exp ((↑(-2*Real.pi*⟪planeCoords.symm p,sineLine j r⟫):ℂ)*Complex.I)*F (planeCoords.symm p) := by
    simpa only [smul_eq_mul,← planeCoords_apply,ContinuousLinearEquiv.symm_apply_apply] using hm
  rw [hr]
  conv_rhs => rw [← sineSlice_integral j]
  apply integral_congr_ae
  filter_upwards [] with p
  change pairMeanCharacter (-p.1*r)*F (planeCoords.symm (sineSliceMap j p)) = _
  rw [sineSlice_dot j p.1 p.2 r]
  congr 1
  simp only [pairMeanCharacter,Complex.ofReal_mul,Complex.ofReal_neg]
  congr 1
  push_cast
  ring

theorem sineLine_fourier_integral (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    (∫ r : ℝ, (𝓕 F) (sineLine j r)) = ∫ r : ℝ, F (sineComplement j r) := by
  let G := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sineSliceEquiv j)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm F)
  have he : 𝓕 (sineMarginal G) = fun r => (𝓕 F) (sineLine j r) :=
    funext (sineSlice_fourier_marginal j F)
  have hi : Integrable (𝓕 (sineMarginal G)) := by
    rw [he]; exact sineLine_integrable j (𝓕 F)
  have h := (sineMarginal_integrable G).fourierInv_fourier_eq hi
    (sineMarginal_continuous G).continuousAt (v := 0)
  rw [Real.fourierInv_eq',he] at h
  simpa [sineMarginal,G,sineComplement,sineSliceEquiv] using h

end
end HigherCorrelations
