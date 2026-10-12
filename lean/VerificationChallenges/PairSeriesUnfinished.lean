import HigherCorrelations.PairSeriesDefinitions
import HigherCorrelations.UniformHeightDefinitions
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Definition-only specifications. Intentional unfinished challenge proofs;
solution modules never import this file. Assumptions: UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairSeries_convergence :
    (∀ X t : ℝ, 1≤X → Summable (fun i => ‖pairZeroTerm i (X,t)‖) ∧
      Summable (fun n => ‖pairPrimeTerm n (X,t)‖)) ∧
    ContinuousOn pairZeroSeries pairSeriesDomain ∧
    ContinuousOn pairPrimeSeries pairSeriesDomain ∧
    (∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
      pairZeroTail X t U ≤ C*Real.sqrt X*Real.log U/U) := by sorry

end
end HigherCorrelations
