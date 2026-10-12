import HigherCorrelations.IntegralProfileDefinitions
import Mathlib.Analysis.Calculus.Taylor

/-! Definition-only Comparator specifications. Intentional unfinished proofs;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory
open scoped Topology

theorem integralProfile_eq (a b e f g : ℝ)
    (he : |e| ≤ 3/4) (hf : |f| ≤ 3/4) (hg : |g| ≤ 3/4) :
    integralProfile a b e f g = rationalProfile a b e f g := by sorry

end
end HigherCorrelations
