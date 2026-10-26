import HigherCorrelations.TripleBudgetDefinitions

/-! UNCONDITIONAL. The logarithmic smoothing mean and its exact J1 remainder.
The whole-line mean agrees with the manuscript integral on [1,2]. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def tripleSmoothingMean (ω : ℝ → ℝ) : ℝ := ∫ u : ℝ, ω u*Real.log u

def tripleSmoothingError (ω : ℝ → ℝ) (T : ℝ) : ℝ :=
  tripleBudgetMoment ω T 1-Real.log T-tripleSmoothingMean ω

end
end HigherCorrelations
