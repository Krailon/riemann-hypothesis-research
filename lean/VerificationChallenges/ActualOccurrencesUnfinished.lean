import HigherCorrelations.ActualCorrelationDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Definition-only specifications. Intentional unfinished terms; solutions never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff FourierTransform SchwartzMap

theorem stripZero_ne_one (ρ : StripZero) : ρ.val ≠ 1  := by sorry

end
end HigherCorrelations
