import HigherCorrelations.UniformHeightDefinitions
import HigherCorrelations.IntegralProfileDefinitions
import Mathlib.Analysis.Complex.JensenFormula

/-! Definition-only specifications. Intentional unfinished proofs for Comparator;
solution modules never import this file. -/
namespace HigherCorrelations
noncomputable section
open Metric Complex Real
open scoped Classical

theorem occurrence_count_local :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      ((occurrenceInterval v (v+1)).card : ℝ) ≤ C*Real.log (|v|+2) := by sorry

end
end HigherCorrelations
