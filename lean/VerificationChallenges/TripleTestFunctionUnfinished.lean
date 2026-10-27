import HigherCorrelations.TripleTestDefinitions
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! UNCONDITIONAL independent specifications. Intentional holes occur only in
verification challenges; project imports contain definitions only. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap

theorem complexFourier_entire (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : Differentiable ℂ (complexFourier φ) := by sorry

theorem tripleTest_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    tripleTestStatistic ω φ T =
      ∫ p, φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by sorry

theorem tripleTest_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0 ≤ W → (∀ u, ω u ≤ W) →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ ε T : ℝ, 0 < ε → ε < 1/3 → 2*Real.pi < T → tsupport φ ⊆ tripleTestMargin ε →
    ‖tripleTestStatistic ω φ T‖ ≤
      C*tripleTestL1 φ*(1+W+fourierDerivativeL1 ω 1)*(tripleTestBase T)^(-ε)*Real.log (2*T+2)^4 := by sorry

theorem tripleTest_interior_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ tripleTestRegion) :
    Tendsto (fun T => tripleTestStatistic ω φ T) atTop (𝓝 0) := by sorry

end
end HigherCorrelations
