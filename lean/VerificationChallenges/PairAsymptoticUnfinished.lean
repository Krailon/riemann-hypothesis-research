import HigherCorrelations.PairAsymptoticDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section

theorem pairNormalized_asymptotic :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ T α : ℝ, 3≤T → |α|≤1 →
      |pairNormalizedCorrelation T α - T^(-2*|α|)*Real.log T - (|α|)| ≤
        C₁*T^(-2*|α|)+C₂/Real.sqrt (Real.log T) := by sorry

end
end HigherCorrelations
