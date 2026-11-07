import HigherCorrelations.SineOverlapDefinitions
import HigherCorrelations.PairMeanDefinitions
import HigherCorrelations.ComplexFourierDefinitions

/-! UNCONDITIONAL definition-only interfaces for bilinear sinc Fourier pairings. -/
namespace HigherCorrelations
noncomputable section

def sineCycle (p : ℝ × ℝ) : ℂ :=
  (pairMeanSinc p.1 : ℂ) * (pairMeanSinc p.2 : ℂ) * (pairMeanSinc (p.1-p.2) : ℂ)
def sineDensityPlane (p : FourierPlane) : ℂ :=
  sineCycleDensity (planeCoords p).1 (planeCoords p).2
def sineCyclePlane (p : FourierPlane) : ℂ := sineCycle (planeCoords p)
def sineParameterIntegrand (u v : ℝ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  pairMeanBox q.1 * pairMeanBox (q.2.1-q.1) * pairMeanBox (q.2.2+q.1) *
    pairMeanCharacter (u*q.2.1+v*q.2.2)

end
end HigherCorrelations
