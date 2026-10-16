import HigherCorrelations.PairSieveWeighted

/-! UNCONDITIONAL. Explicit cutoff and normalization endpoint checks. -/
namespace HigherCorrelations
noncomputable section

theorem pairMeanPrimeNearby_zero (X : ℝ) : pairMeanPrimeNearby X 0 = 0 := by
  simp [pairMeanPrimeNearby, not_lt_of_ge (abs_nonneg _)]

theorem pairMeanPrimeNearby_endpoint (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimeNearby X (1/2) ≤ pairSieveNearbyConstant*X/2 := by
  have := pairMeanPrimeNearby_bound X (1/2) hX (by norm_num) le_rfl
  linarith

theorem pairMeanPrimeNearby_unit (δ : ℝ) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2) :
    pairMeanPrimeNearby 1 δ ≤ pairSieveNearbyConstant*δ := by
  simpa using pairMeanPrimeNearby_bound 1 δ le_rfl hδ hδhi

/-- A pair exactly on the logarithmic boundary is excluded. -/
theorem pairMeanPrimeNearby_boundary_term (X δ : ℝ) (m n : ℕ)
    (he : |Real.log ((m+1:ℝ)/(n+1:ℝ))| = 2*Real.pi*δ) :
    (if m ≠ n ∧ |Real.log ((m+1:ℝ)/(n+1:ℝ))| < 2*Real.pi*δ then
      pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n else 0) = 0 := by
  simp [he]
end
end HigherCorrelations
