import HigherCorrelations.PairRHSDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL definition-only statement specifications.
Unfinished challenge proofs are isolated from the solution import graph. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHSMean_uniform : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    pairRHSSquare X T = pairZeroMeanSquare X T ∧
    pairRHSSquare X T = T*Real.log T^2/X^2+T*Real.log X+
      pairRHSSmallError X T+pairRHSLargeError X T ∧
    |pairRHSSmallError X T| ≤ C₁*(T*Real.log T/X^2) ∧
    |pairRHSLargeError X T| ≤ C₂*(T*Real.sqrt (Real.log T)) := by sorry

end
end HigherCorrelations
