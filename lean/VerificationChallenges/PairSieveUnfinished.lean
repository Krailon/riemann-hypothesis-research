import HigherCorrelations.PairSieveDefinitions

/-! Isolated rejection control: this is not a solution module. -/
namespace HigherCorrelations
noncomputable section
theorem pairMeanPrimeNearby_bound (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2) :
    pairMeanPrimeNearby X δ ≤ pairSieveNearbyConstant*δ*X := by sorry
end
end HigherCorrelations
