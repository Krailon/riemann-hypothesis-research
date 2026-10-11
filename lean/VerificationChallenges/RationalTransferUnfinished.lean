import HigherCorrelations.RationalTransferDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Definition-only Comparator specifications. Intentional unfinished proofs;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology ContDiff

theorem rational_denominator_lower (z : ℂ) (hz : |z.im| ≤ 1) :
    3 + z.re ^ 2 ≤ ‖4 + z ^ 2‖ := by sorry

end
end HigherCorrelations
