import HigherCorrelations.PairPrimeMeanDefinitions

/-! UNCONDITIONAL independent statement specifications. Deliberately unfinished
challenge proofs are isolated from all solution imports. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairPrimeMean_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    |pairPrimeMeanOffdiag X T| ≤ C*Real.sqrt (T*X*Real.log (2*X)) ∧
    |pairPrimeMeanDiagonalError X T| ≤ C*T ∧
    pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)) := by sorry
end
end HigherCorrelations
