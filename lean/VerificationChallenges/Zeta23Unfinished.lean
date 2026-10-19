import HigherCorrelations.Zeta23Definitions

namespace HigherCorrelations
noncomputable section
theorem zeta23_dyadic_occurrences :
    ∃ C T₀ : ℝ, 0 < C ∧ 3 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      |((occurrenceWindow T (2*T)).card : ℝ) - zetaDyadicMain T| ≤ C * Real.log T := by sorry

end
end HigherCorrelations
