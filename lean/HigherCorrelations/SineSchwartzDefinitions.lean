import HigherCorrelations.SineBenchmarkDefinitions

/-! UNCONDITIONAL continuous restriction maps with coordinate line measure. -/
namespace HigherCorrelations
noncomputable section
open scoped SchwartzMap

def sinePairLineRestriction (j : Fin 3) : 𝓢(ℝ × ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (sineLineCoords j).hasTemperateGrowth
    (show AntilipschitzWith 1 (sineLineCoords j) from by
      intro x y
      fin_cases j <;> simp [sineLineCoords,edist_dist,dist_eq_norm,Prod.norm_def])

def sineLineRestriction (j : Fin 3) : 𝓢(FourierPlane,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  (sinePairLineRestriction j).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm)

def sineComplementRestriction (j : Fin 3) : 𝓢(FourierPlane,ℂ) →L[ℂ] 𝓢(ℝ,ℂ) :=
  (sinePairLineRestriction 1).comp
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (sineSliceEquiv j)).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeCoords.symm))

end
end HigherCorrelations
