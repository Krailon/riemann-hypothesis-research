import HigherCorrelations.TripleTestEndpoints

/-! UNCONDITIONAL interior weighted test-function theorem, with full zeros.
The absolute constants are existential. Cutoffs are removed at fixed parameters;
only afterwards is the height sent to infinity for fixed test and smoothing. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleTest_independent_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      8*∑ v ∈ tripleDomain S, tripleMasterKernel ω T (tripleTestToMaster v)*
        complexFourier φ (tripleTestArguments T v)) atTop (𝓝 (tripleTestStatistic ω φ T)) := by
  exact (triple_cutoff_limit _ (tripleTest_zero_sum_absolute ω hω φ hφ hc ε T hε hT hs)).const_mul 8

theorem tripleTest_theorem : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0 ≤ W → (∀ u, ω u ≤ W) →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ ε T : ℝ, 0 < ε → ε < 1/3 → 2*Real.pi < T → tsupport φ ⊆ tripleTestMargin ε →
    Differentiable ℂ (complexFourier φ) ∧
    Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier φ (tripleTestArguments T v)‖) ∧
    tripleTestStatistic ω φ T =
      (∫ p, φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) ∧
    ‖tripleTestStatistic ω φ T‖ ≤ C*tripleTestL1 φ*(1+W+fourierDerivativeL1 ω 1)*
      (tripleTestBase T)^(-ε)*Real.log (2*T+2)^4 ∧
    Tendsto (fun U => tripleTestStatistic ω φ U) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := tripleTest_bound
  refine ⟨C,hC,?_⟩
  intro ω hω W hW hw φ hφ hc ε T hε he hT hs
  exact ⟨complexFourier_entire φ hφ hc,tripleTest_zero_sum_absolute ω hω φ hφ hc ε T hε hT hs,
    tripleTest_identity ω hω φ hφ hc ε T hε hT hs,h ω hω W hW hw φ hφ hc ε T hε he hT hs,
    tripleTest_fixed_margin_limit ω hω φ hφ hc ε hε he hs⟩

end
end HigherCorrelations
