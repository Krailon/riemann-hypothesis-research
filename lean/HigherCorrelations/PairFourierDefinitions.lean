import HigherCorrelations.PairAsymptoticDefinitions
import HigherCorrelations.ActualCorrelationDefinitions

/-! UNCONDITIONAL definition-only pair Fourier interface. The one-dimensional
transform here has the negative sign, unlike the existing inverse plane transform. -/
namespace HigherCorrelations
noncomputable section

def pairComplexFourier (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ a : ℝ, g a * Complex.exp (-2*Real.pi*Complex.I*z*a)
def pairSourceSpacing (T : ℝ) : ℝ := Real.log T/(2*Real.pi)
def pairScaleRatio (T : ℝ) : ℝ := pairSourceSpacing T/meanSpacing T
def pairNormalization (T : ℝ) : ℝ := T*Real.log T/(2*Real.pi)
def pairLocalCorrelation (T ξ : ℝ) : ℝ :=
  (pairCorrelationSum ((T/(2*Real.pi))^ξ) T).re/(T*meanSpacing T)
def pairHorizontalCoordinate (T : ℝ) (i : ZeroOccurrence) : ℝ :=
  occurrenceDisplacement i*Real.log T
def pairDifferenceWeight (z : ℂ) : ℂ := 4/(4-z^2)
def pairFrequencyTerm (T a : ℝ) (i j : ZeroOccurrence) : ℂ :=
  Complex.exp ((a*Real.log T : ℝ)*(occurrenceValue i-occurrenceValue j)) *
    pairDifferenceWeight (occurrenceValue i-occurrenceValue j)
def pairFourierStatistic (T : ℝ) (g : ℝ → ℂ) : ℂ :=
  (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
    pairDifferenceWeight (occurrenceValue i-occurrenceValue j)*
      pairComplexFourier g (Complex.I*pairSourceSpacing T*(occurrenceValue i-occurrenceValue j))) /
        (pairNormalization T : ℂ)
def pairFourierPeak (q a : ℝ) : ℝ := q*Real.exp (-2*q*|a|)
def pairFourierMain (g : ℝ → ℂ) : ℂ := g 0 + ∫ a : ℝ, ((|a| : ℝ) : ℂ)*g a

end
end HigherCorrelations
