import HigherCorrelations.SineBenchmarkDefinitions

/-! UNCONDITIONAL bilinear benchmark functionals and ordinary/factorial conventions. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

def sinePlanePair (f : FourierPlane → ℂ) (F : 𝓢(FourierPlane,ℂ)) : ℂ := ∫ p, F p*f p
def sineLinePair (j : Fin 3) (w : ℝ → ℂ) (F : 𝓢(FourierPlane,ℂ)) : ℂ := ∫ r, F (sineLine j r)*w r
def sineComplementPair (j : Fin 3) (w : ℝ → ℂ) (F : 𝓢(FourierPlane,ℂ)) : ℂ := ∫ r, F (sineComplement j r)*w r

def sineDifferenceForm (j : Fin 3) (p : FourierPlane) : ℝ :=
  ![(planeCoords p).2,(planeCoords p).1,(planeCoords p).1-(planeCoords p).2] j

def sineBenchmarkRow (k : TriplePattern) (F : 𝓢(FourierPlane,ℂ)) : ℂ :=
  match k with
  | .allEqual => F 0
  | .only01 => sineLinePair 1 sineR2 F
  | .only02 => sineLinePair 0 sineR2 F
  | .only12 => sineLinePair 2 sineR2 F
  | .allDistinct => sinePlanePair (fun p => sineR3 (planeCoords p)) F

def sineBenchmark (F : 𝓢(FourierPlane,ℂ)) : ℂ := ∑ k : TriplePattern, sineBenchmarkRow k F

def sineCovarianceLift (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) : ℂ :=
  sineLinePair j (fun _ => 1) F-sinePlanePair (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2) F

def sineOrdinaryCumulant (F : 𝓢(FourierPlane,ℂ)) : ℂ :=
  F 0 - (∑ j : Fin 3, sineLinePair j (fun r => (pairMeanSinc r:ℂ)^2) F) +
    2*sinePlanePair sineCyclePlane F

def sineFactorialCumulant (F : 𝓢(FourierPlane,ℂ)) : ℂ := 2*sinePlanePair sineCyclePlane F

def sineBenchmarkSpectrum (F : 𝓢(FourierPlane,ℂ)) : ℂ :=
  F 0 + (∑ j : Fin 3, sineComplementPair j (fun r => 1-(pairMeanTriangle r:ℂ)) F) +
    sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F

def sineBenchmarkFourierRow (k : TriplePattern) (F : 𝓢(FourierPlane,ℂ)) : ℂ :=
  match k with
  | .allEqual => sinePlanePair (fun _ => 1) F
  | .only01 => sineComplementPair 1 (fun _ => 1) F-sinePlanePair (fun p => (pairMeanTriangle (sineLineForm 1 p):ℂ)) F
  | .only02 => sineComplementPair 0 (fun _ => 1) F-sinePlanePair (fun p => (pairMeanTriangle (sineLineForm 0 p):ℂ)) F
  | .only12 => sineComplementPair 2 (fun _ => 1) F-sinePlanePair (fun p => (pairMeanTriangle (sineLineForm 2 p):ℂ)) F
  | .allDistinct => F 0-(∑ j : Fin 3, sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F)+2*sinePlanePair sineDensityPlane F

end
end HigherCorrelations
