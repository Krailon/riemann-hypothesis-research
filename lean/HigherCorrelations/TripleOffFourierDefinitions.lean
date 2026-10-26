import HigherCorrelations.TripleLogGapDefinitions
import HigherCorrelations.PairMeanDefinitions

/-! UNCONDITIONAL definition-only interface for grouped integer frequencies. -/
namespace HigherCorrelations
noncomputable section

def tripleLogFrequency (n : LogGapIndex) : ℝ := -Real.log n.val/(2*Real.pi)

def tripleLogFourierTerm (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (p : LogGapIndex × LogGapIndex) : ℂ :=
  c p.1*star (d p.2)*pairMeanFourier (fun u => (φ u:ℂ))
    (T/(2*Real.pi)*Real.log ((p.1.val:ℝ)/p.2.val))

def tripleLogFourierOffTerm (φ : ℝ → ℝ) (T : ℝ) (c d : LogGapIndex → ℂ)
    (p : LogGapIndex × LogGapIndex) : ℂ :=
  if p.1=p.2 then 0 else tripleLogFourierTerm φ T c d p

end
end HigherCorrelations
