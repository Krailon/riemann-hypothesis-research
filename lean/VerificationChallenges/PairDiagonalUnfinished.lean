import HigherCorrelations.PairDiagonalDefinitions

/-! Isolated rejection control, never imported by a solution. -/
namespace HigherCorrelations
noncomputable section
theorem pairMeanPrimeDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-Real.log X| ≤ C := by sorry
end
end HigherCorrelations
