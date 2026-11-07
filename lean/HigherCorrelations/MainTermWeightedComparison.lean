import HigherCorrelations.MainTermSupportComparison
import HigherCorrelations.ProfileTransferLimits
import HigherCorrelations.ProfileLocalNormalization

/-! UNCONDITIONAL weighted benchmark comparison. Constants retain their inherited
existential status; signed and kernel errors stay separate. Strict support margin
for the zero statistics; all complex arguments and horizontal weights retained. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology SchwartzMap FourierTransform

theorem mainTerm_signed_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0≤W → (∀ u, ω u≤W) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1≤T → 0<κ → tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*signedC1 φ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by
  obtain ⟨C,hC,h⟩ := signed_uniform_bound
  refine ⟨C,hC,?_⟩
  intro ω hω W hW hw φ hφ hc T κ hT hκ hs
  simpa only [mainTermComparison_margin φ hφ hc κ hκ.le hs] using
    h ω hω W hW hw φ hφ hc T κ hT hκ hs

theorem mainTerm_frozen_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ (M₀ : ℝ) (M₁ : ℝ≥0),
    0≤M₀ → (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+(M₁:ℝ))*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨A,C,hA,hC,h⟩ := frozenStatistic_uniform_bound
  refine ⟨A,C,hA,hC,?_⟩
  intro ω hω M₀ M₁ hM₀ hw hl φ hφ hc κ T hκ hT hs
  simpa only [mainTermComparison_margin φ hφ hc κ hκ.le hs] using
    h ω hω M₀ M₁ hM₀ hw hl φ hφ hc κ T hκ hT hs

theorem mainTerm_frozen_bound_deriv : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+M₁)*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨A,C,hA,hC,h⟩ := mainTerm_frozen_bound
  refine ⟨A,C,hA,hC,?_⟩
  intro ω hω M₀ M₁ hM₀ hM₁ hw hd φ hφ hc κ T hκ hT hs
  apply h ω hω M₀ ⟨M₁,hM₁⟩ hM₀ hw _ φ hφ hc κ T hκ hT hs
  exact lipschitzWith_of_nnnorm_deriv_le (hω.smooth.differentiable (by simp)) (fun u => by
    change ‖deriv ω u‖≤M₁
    simpa only [Real.norm_eq_abs] using hd u)

theorem mainTerm_signed_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  simpa only [mainTermComparison_margin φ hφ hc κ hκ.le hs] using
    signed_fixed_margin_limit ω hω φ hφ hc κ hκ hs

theorem mainTerm_frozen_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  simpa only [mainTermComparison_margin φ hφ hc κ hκ.le hs] using
    frozenStatistic_fixed_margin_limit ω hω φ hφ hc κ hκ hs

theorem mainTerm_signed_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  obtain ⟨κ,hκ,hκ1,hm⟩ := signed_compact_margin φ hc hs
  exact mainTerm_signed_limit ω hω φ hφ hc κ hκ hm

theorem mainTerm_frozen_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  obtain ⟨κ,hκ,hκ1,hm⟩ := signed_compact_margin φ hc hs
  exact mainTerm_frozen_limit ω hω φ hφ hc κ hκ hm

theorem mainTerm_signed_normalized_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => (2/3:ℂ)*signedStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  have hh := (mainTerm_signed_limit ω hω φ hφ hc κ hκ hs).const_mul (2/3:ℂ)
  have he : (2/3:ℂ)*((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)) =
      sineBenchmark (mainTermPhysicalTest φ hφ hc) := by ring
  rwa [he] at hh

theorem mainTerm_frozen_normalized_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => (2/3:ℂ)*frozenStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  have hh := (mainTerm_frozen_limit ω hω φ hφ hc κ hκ hs).const_mul (2/3:ℂ)
  have he : (2/3:ℂ)*((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)) =
      sineBenchmark (mainTermPhysicalTest φ hφ hc) := by ring
  rwa [he] at hh

end
end HigherCorrelations
