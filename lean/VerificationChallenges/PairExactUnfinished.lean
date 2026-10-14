import HigherCorrelations.PairExactDefinitions

/-! Intentional negative control, never imported by a solution. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section

theorem pairExact_formula (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t)-pairShiftCorrection (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by sorry

end
end HigherCorrelations
