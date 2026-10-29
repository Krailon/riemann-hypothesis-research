import HigherCorrelations.TripleQuadrantDefinitions

/-! UNCONDITIONAL definitions of the three leading frequency contributions. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

def tripleQuadrantOriginLead (ψ : ℝ × ℝ → ℂ) (b : ℝ) : ℂ :=
  ∫ p in tripleQuadrant, ψ p*(Real.exp (-(2*b*(p.1+p.2))):ℂ)

def tripleQuadrantAxisKernel (b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1+b*p.2)*(b*p.1+b*p.2/2)*Real.exp (-(2*b*p.2))

def tripleQuadrantAxisLead (ψ : ℝ × ℝ → ℂ) (b : ℝ) : ℂ :=
  ∫ p in tripleQuadrant, ψ p*(tripleQuadrantAxisKernel b p:ℂ)

def tripleQuadrantAxisScaled (ψ : ℝ × ℝ → ℂ) (b r : ℝ) : ℂ :=
  ∫ t : ℝ in Ici 0,
    ψ (r,t/b)*(((1+t)*(r+t/(2*b))*Real.exp (-(2*t)):ℝ):ℂ)

end
end HigherCorrelations
