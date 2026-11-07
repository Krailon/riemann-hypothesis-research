import HigherCorrelations.MainTermWeightedComparison

/-! UNCONDITIONAL weighted comparison with the all-ordered sine benchmark.
The deterministic identity includes the boundary; the zeta limits do not. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap

theorem mainTermPhysicalTest_zero (hφ : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ × ℝ → ℂ))
    (hc : HasCompactSupport (0 : ℝ × ℝ → ℂ)) :
    mainTermPhysicalTest 0 hφ hc = 0 := by
  ext x
  rw [mainTermPhysicalTest_apply]
  simp [complexFourier]

theorem mainTermBenchmark_zero (hφ : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ × ℝ → ℂ))
    (hc : HasCompactSupport (0 : ℝ × ℝ → ℂ)) :
    sineBenchmark (mainTermPhysicalTest 0 hφ hc) = 0 := by
  rw [mainTermPhysicalTest_zero,sineBenchmark_five]
  simp [sinePlanePair,sineLinePair]

theorem mainTerm_signed_normalized_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => (2/3:ℂ)*signedStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  obtain ⟨κ,hκ,hκ1,hm⟩ := signed_compact_margin φ hc hs
  exact mainTerm_signed_normalized_limit ω hω φ hφ hc κ hκ hm

theorem mainTerm_frozen_normalized_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => (2/3:ℂ)*frozenStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  obtain ⟨κ,hκ,hκ1,hm⟩ := signed_compact_margin φ hc hs
  exact mainTerm_frozen_normalized_limit ω hω φ hφ hc κ hκ hm

end
end HigherCorrelations
