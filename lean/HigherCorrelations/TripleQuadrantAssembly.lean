import HigherCorrelations.TripleQuadrantIdentity
import HigherCorrelations.QuadrantFourierRegularity

/-! UNCONDITIONAL exact quadrant passage. This module asserts no height
asymptotic: its absolute convergence holds at each fixed T > 2 pi. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleQuadrant_entire (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    Differentiable ℂ (tripleQuadrantFourier ψ) :=
  complexFourier_indicator_entire tripleQuadrant tripleQuadrant_measurable ψ hψ hc

theorem tripleQuadrant_normalized_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) :
    tripleQuadrantStatistic ω ψ T =
      (∫ p in tripleQuadrant, ψ p*tripleMasterObservable ω T
        ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2))/(Real.log T:ℂ) := by
  rw [tripleQuadrantStatistic,tripleQuadrant_identity ω hω ψ hψ hc κ T hκ hT hs]
  congr 1
  rw [← integral_indicator tripleQuadrant_measurable]
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hp : p ∈ tripleQuadrant <;> simp [tripleQuadrantAmplitude,hp]

theorem tripleQuadrant_zero_identity (ω : ℝ → ℝ) (ψ : ℝ × ℝ → ℂ) (T : ℝ) :
    tripleQuadrantStatistic ω ψ T = (8/(Real.log T:ℂ))*
      ∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)*
        tripleQuadrantFourier ψ (tripleTestArguments T v) := by
  unfold tripleQuadrantStatistic tripleTestStatistic tripleQuadrantFourier
  ring

theorem tripleQuadrant_independent_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (κ T : ℝ) (hκ : 0<κ) (hT : 2*Real.pi<T)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      (8/(Real.log T:ℂ))*∑ v ∈ tripleDomain S,
        tripleMasterKernel ω T (tripleTestToMaster v)*
          tripleQuadrantFourier ψ (tripleTestArguments T v)) atTop
      (𝓝 (tripleQuadrantStatistic ω ψ T)) := by
  rw [tripleQuadrant_zero_identity]
  exact (triple_cutoff_limit _
    (tripleQuadrant_zero_sum_absolute ω hω ψ hψ hc κ T hκ hT hs)).const_mul _

end
end HigherCorrelations
