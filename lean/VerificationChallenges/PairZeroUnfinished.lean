import HigherCorrelations.PairZeroDefinitions

/-! Independent statement surface; intentional holes belong only to the challenge. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

theorem pairZero_decomposition (X T Z : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (_hZ : 0 ≤ Z) :
    pairZeroMeanSquare X T = 2*Real.pi*(pairCorrelationSum X T).re +
      pairZeroTruncError X T Z + pairZeroHeightError X T Z + pairZeroExtensionError X T := by sorry

end
end HigherCorrelations
