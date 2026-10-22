import HigherCorrelations.PairFourierDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology FourierTransform

theorem pairFourier_tendsto (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1) :
    Tendsto (fun T : ℝ => pairFourierStatistic T g) atTop (𝓝 (pairFourierMain g)) := by sorry

end
end HigherCorrelations
