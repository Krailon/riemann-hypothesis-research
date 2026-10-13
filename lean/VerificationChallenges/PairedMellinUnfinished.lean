import HigherCorrelations.PairedMellinDefinitions

/-! Definition-only specifications. Intentional unfinished challenge proofs;
solution modules never import this file. Assumptions: UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter
open scoped Topology

theorem pairedMellin_kernel (y : ℝ) (hy : 0<y) :
    Integrable (pairedMellinIntegrand y) ∧
    pairedMellinUpwardIntegral y = if 1<y then (y:ℂ)-(y:ℂ)⁻¹ else 0 := by sorry

end
end HigherCorrelations
