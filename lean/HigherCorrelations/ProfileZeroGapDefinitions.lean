import HigherCorrelations.RationalTransferDefinitions

/-! UNCONDITIONAL definition-only real zero-gap horizontal profile.
The conjugated anchor gives sums e+g and f+g, while the first pair gives e-f.
Analytic identification and positivity are asserted separately on the closed cube. -/
namespace HigherCorrelations
noncomputable section

def zeroGapHorizontalDenominator (e f g : ℝ) : ℝ :=
  (4-(e-f)^2)*(4-(e+g)^2)*(4-(f+g)^2)

def zeroGapHorizontalProfile (e f g : ℝ) : ℝ :=
  Real.pi*(24-(e-f)^2-(e+g)^2-(f+g)^2)/zeroGapHorizontalDenominator e f g

end
end HigherCorrelations
