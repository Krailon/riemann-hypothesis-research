import HigherCorrelations.MainTermComparisonDefinitions

/-! Expected contracts only; deliberately unfinished for the Comparator. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology SchwartzMap FourierTransform

theorem mainTermFrequencyTest_apply (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x : FourierPlane) :
    mainTermFrequencyTest φ hφ hc x = φ (planeCoords x) := by sorry

theorem mainTermPhysicalTest_apply (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x : FourierPlane) :
    mainTermPhysicalTest φ hφ hc x =
      complexFourier φ (((planeCoords x).1:ℂ),((planeCoords x).2:ℂ)) := by sorry

theorem mainTermPhysicalTest_fourier (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    𝓕 (mainTermPhysicalTest φ hφ hc) = mainTermFrequencyTest φ hφ hc := by sorry

theorem sineR2_reflection (r : ℝ) : sineR2 (-r) = sineR2 r := by sorry

theorem sineR3_reflection (p : ℝ × ℝ) : sineR3 (-p) = sineR3 p := by sorry

theorem sineBenchmark_reflection (F G : 𝓢(FourierPlane,ℂ))
    (hG : ∀ x, G x = F (-x)) : sineBenchmark G = sineBenchmark F := by sorry

theorem sineBenchmark_inverse_pairing (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark (𝓕⁻ F) = sineBenchmarkSpectrum F := by sorry

theorem sineComplement_gauge (j : Fin 3) (r : ℝ) :
    signedGauge (planeCoords (sineComplement j r)) = |r| := by sorry

theorem sineBenchmark_planar_zero (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) :
    sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F = 0 := by sorry

theorem sineBenchmark_line_weight (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) (j : Fin 3) (r : ℝ) :
    F (sineComplement j r)*(1-(pairMeanTriangle r:ℂ)) =
      ((|r|:ℝ):ℂ)*F (sineComplement j r) := by sorry

theorem sineBenchmark_trace_integrable (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) (j : Fin 3) :
    Integrable (fun r : ℝ => ((|r|:ℝ):ℂ)*F (sineComplement j r)) := by sorry

theorem sineBenchmarkSpectrum_closed (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) :
    sineBenchmarkSpectrum F = F 0 + ∫ r : ℝ, ((|r|:ℝ):ℂ)*
      (F (planeCoords.symm (r,0))+F (planeCoords.symm (0,r))+F (planeCoords.symm (r,-r))) := by sorry

theorem mainTermBenchmark_closed (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p | signedGauge p ≤ 1}) :
    sineBenchmark (mainTermPhysicalTest φ hφ hc) = φ (0,0)+
      ∫ r : ℝ, ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r)) := by sorry

theorem mainTermBenchmark_margin (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hs : tsupport φ ⊆ signedMargin κ) :
    sineBenchmark (mainTermPhysicalTest φ hφ hc) = φ (0,0)+
      ∫ r : ℝ, ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r)) := by sorry

theorem mainTermComparison_exact (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p | signedGauge p ≤ 1}) :
    signedLimit φ = (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc) := by sorry

theorem mainTermComparison_margin (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hs : tsupport φ ⊆ signedMargin κ) :
    signedLimit φ = (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc) := by sorry

theorem mainTerm_signed_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0≤W → (∀ u, ω u≤W) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1≤T → 0<κ → tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*signedC1 φ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by sorry

theorem mainTerm_frozen_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ (M₀ : ℝ) (M₁ : ℝ≥0),
    0≤M₀ → (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+(M₁:ℝ))*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem mainTerm_frozen_bound_deriv : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-(3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+M₁)*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem mainTerm_signed_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_frozen_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_signed_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_frozen_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 ((3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_signed_normalized_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => (2/3:ℂ)*signedStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_frozen_normalized_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => (2/3:ℂ)*frozenStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTermPhysicalTest_zero (hφ : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ × ℝ → ℂ))
    (hc : HasCompactSupport (0 : ℝ × ℝ → ℂ)) :
    mainTermPhysicalTest 0 hφ hc = 0 := by sorry

theorem mainTermBenchmark_zero (hφ : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ × ℝ → ℂ))
    (hc : HasCompactSupport (0 : ℝ × ℝ → ℂ)) :
    sineBenchmark (mainTermPhysicalTest 0 hφ hc) = 0 := by sorry

theorem mainTerm_signed_normalized_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => (2/3:ℂ)*signedStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem mainTerm_frozen_normalized_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => (2/3:ℂ)*frozenStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

end
end HigherCorrelations
