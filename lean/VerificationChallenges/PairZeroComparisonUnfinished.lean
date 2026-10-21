import HigherCorrelations.PairZeroBoundDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroComparison_uniform :
    ∃ Ct Cx : ℝ, 0 < Ct ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T → X ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤ Ct*T+Cx*X := by sorry

end
end HigherCorrelations
