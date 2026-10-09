import HigherCorrelations.SummabilityDefinitions

/-! Definition-only specifications. Intentional sorry terms; solutions never import this file. -/
namespace HigherCorrelations
open Filter MeasureTheory
open scoped Topology

theorem dyadic_ratio_bounds (d p : ℕ) (hp : d < p) :
    0 ≤ dyadicRatio d p ∧ dyadicRatio d p < 1 := by sorry

end HigherCorrelations
