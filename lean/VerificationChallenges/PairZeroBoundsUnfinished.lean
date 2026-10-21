import HigherCorrelations.PairZeroBoundDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroUniformBounds :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*
          (Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) ∧
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*Real.log Z^2/Z ∧
        |pairZeroHeightError X T Z| ≤ Ch*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤ Ce*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by sorry

end
end HigherCorrelations
