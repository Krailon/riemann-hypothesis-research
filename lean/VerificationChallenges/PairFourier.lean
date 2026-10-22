import HigherCorrelations.PairFourierDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology FourierTransform

theorem pairComplexFourier_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (z : ℂ) :
    Integrable (fun a : ℝ => g a*Complex.exp (-2*Real.pi*Complex.I*z*a)) := by sorry

theorem pairComplexFourier_real (g : ℝ → ℂ) (x : ℝ) :
    pairComplexFourier g x = 𝓕 g x := by sorry

theorem pairComplexFourier_zero_argument (g : ℝ → ℂ) :
    pairComplexFourier g 0 = ∫ a : ℝ, g a := by sorry

theorem pairComplexFourier_argument (g : ℝ → ℂ) (T : ℝ) (z : ℂ) :
    pairComplexFourier g (Complex.I*pairSourceSpacing T*z) =
      ∫ a : ℝ, g a*Complex.exp ((a*Real.log T : ℝ)*z) := by sorry

theorem pairFrequencyTerm_sum (T a : ℝ) (hT : 0<T) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i j) =
      pairCorrelationSum (T^a) T := by sorry

theorem pairFrequencyTerm_continuous (T : ℝ) (i j : ZeroOccurrence) :
    Continuous (fun a => pairFrequencyTerm T a i j) := by sorry

theorem pairNormalizedCorrelation_continuous (T : ℝ) (hT : 0<T) :
    Continuous (pairNormalizedCorrelation T) := by sorry

theorem pairFourierStatistic_integrable (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (T : ℝ) (hT : 0<T) :
    Integrable (fun a => g a*(pairNormalizedCorrelation T a : ℂ)) := by sorry

theorem pairFourierStatistic_identity (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (T : ℝ) (hT : 3≤T) :
    pairFourierStatistic T g = ∫ a : ℝ, g a*(pairNormalizedCorrelation T a : ℂ) := by sorry

theorem pairFrequencyTerm_horizontal (T a : ℝ) (i j : ZeroOccurrence) :
    pairFrequencyTerm T a i j =
      4*Complex.exp ((a*(pairHorizontalCoordinate T i-pairHorizontalCoordinate T j) : ℝ) +
        Complex.I*(a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T : ℝ)) /
      (4-((occurrenceValue i).re-(occurrenceValue j).re : ℂ)^2+
        (occurrenceOrdinate i-occurrenceOrdinate j : ℂ)^2-
        2*Complex.I*((occurrenceValue i).re-(occurrenceValue j).re : ℂ)*
          (occurrenceOrdinate i-occurrenceOrdinate j : ℂ)) := by sorry

theorem pairFrequencyTerm_diagonal (T a : ℝ) (i j : ZeroOccurrence)
    (h : occurrenceValue i = occurrenceValue j) : pairFrequencyTerm T a i j = 1 := by sorry

theorem pairFrequencyTerm_index_diagonal (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i i) =
      ((occurrenceWindow 0 T).card : ℂ) := by sorry

theorem pairWindow_fiber_card (T : ℝ) (ρ : StripZero) (hρ : 0<ρ.val.im ∧ ρ.val.im≤T) :
    ((occurrenceWindow 0 T).filter (fun i => i.1=ρ)).card = zeroMultiplicity ρ := by sorry

theorem pairFrequencyTerm_equal_zero_diagonal (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ (occurrenceWindow 0 T).filter
        (fun j => occurrenceValue j = occurrenceValue i), pairFrequencyTerm T a i j) =
      ∑ ρ ∈ (occurrenceWindow 0 T).image (fun i => i.1), (zeroMultiplicity ρ : ℂ)^2 := by sorry

theorem pairFrequencyTerm_reflection (T a : ℝ) :
    (∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T, pairFrequencyTerm T a i j) =
      ∑ i ∈ occurrenceWindow 0 T, ∑ j ∈ occurrenceWindow 0 T,
        Complex.exp ((a*Real.log T : ℝ)*(occurrenceValue i+star (occurrenceValue j)-1))*
          pairDifferenceWeight (occurrenceValue i+star (occurrenceValue j)-1) := by sorry

theorem pairScale_positive (T : ℝ) (hT : 2*Real.pi<T) :
    0 < meanSpacing T ∧ 0<pairSourceSpacing T ∧ 0<pairScaleRatio T := by sorry

theorem pairScale_normalization (T : ℝ) (hT : 2*Real.pi<T) :
    pairNormalization T = pairScaleRatio T*T*meanSpacing T := by sorry

theorem pairScale_argument (T : ℝ) (hT : 2*Real.pi<T) (i j : ZeroOccurrence) :
    Complex.I*pairSourceSpacing T*(occurrenceValue i-occurrenceValue j) =
      (pairScaleRatio T*(meanSpacing T*(occurrenceOrdinate j-occurrenceOrdinate i)) : ℝ) +
        Complex.I*((pairHorizontalCoordinate T i-pairHorizontalCoordinate T j)/(2*Real.pi) : ℝ) := by sorry

theorem pairScale_phase (T a : ℝ) (hT : 2*Real.pi<T) (i j : ZeroOccurrence) :
    Complex.exp (Complex.I*(a*(occurrenceOrdinate i-occurrenceOrdinate j)*Real.log T : ℝ)) =
      Complex.exp (-2*Real.pi*Complex.I*(pairScaleRatio T*a : ℝ)*
        (meanSpacing T*(occurrenceOrdinate j-occurrenceOrdinate i) : ℝ)) := by sorry

theorem pairScale_support (T a : ℝ) (hT : 2*Real.pi<T) :
    |a|≤1 ↔ |pairScaleRatio T*a|≤pairScaleRatio T := by sorry

theorem pairScale_power (T ξ : ℝ) (hT : 2*Real.pi<T) :
    (T/(2*Real.pi))^ξ = T^(ξ/pairScaleRatio T) := by sorry

theorem pairScale_correlation (T ξ : ℝ) (hT : 2*Real.pi<T) :
    pairLocalCorrelation T ξ = pairScaleRatio T*pairNormalizedCorrelation T (ξ/pairScaleRatio T) := by sorry

theorem pairScale_jacobian (T : ℝ) (hT : 2*Real.pi<T) (f : ℝ → ℂ) :
    (∫ ξ : ℝ, f (ξ/pairScaleRatio T)) =
      (pairScaleRatio T : ℂ)*(∫ a : ℝ, f a) := by sorry

theorem pairScale_integrated (T : ℝ) (hT : 2*Real.pi<T) (g : ℝ → ℂ) :
    (∫ ξ : ℝ, g (ξ/pairScaleRatio T)*(pairLocalCorrelation T ξ : ℂ)) =
      (pairScaleRatio T : ℂ)^2*(∫ a : ℝ, g a*(pairNormalizedCorrelation T a : ℂ)) := by sorry

theorem pairFourierPeak_nonneg (q a : ℝ) (hq : 0≤q) : 0≤pairFourierPeak q a := by sorry

theorem pairFourierPeak_integrable (q : ℝ) (hq : 0<q) : Integrable (pairFourierPeak q) := by sorry

theorem pairFourierPeak_mass (q : ℝ) (hq : 0<q) :
    (∫ a : ℝ, pairFourierPeak q a) = 1 := by sorry

theorem pairFourierPeak_moment_integrable (q : ℝ) (hq : 0<q) :
    Integrable (fun a : ℝ => |a| *pairFourierPeak q a) := by sorry

theorem pairFourierPeak_moment (q : ℝ) (hq : 0<q) :
    (∫ a : ℝ, |a| *pairFourierPeak q a) = 1/(2*q) := by sorry

theorem pairFourierPeak_approximation (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (M : ℝ) (hM : ∀ a : ℝ, ‖g a-g 0‖≤M*|a|)
    (q : ℝ) (hq : 0<q) :
    ‖(∫ a : ℝ, g a*(pairFourierPeak q a : ℂ))-g 0‖≤M/(2*q) := by sorry

theorem pairFourierTest_bounds (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) :
    ∃ M₀ M₁ : ℝ, 0≤M₀ ∧ 0≤M₁ ∧ (∀ a, ‖g a‖≤M₀) ∧
      (∀ a, ‖deriv g a‖≤M₁) ∧ (∀ a : ℝ, ‖g a-g 0‖≤M₁*|a|) := by sorry

theorem pairFourierPeak_power (T a : ℝ) (hT : 0<T) :
    pairFourierPeak (Real.log T) a = T^(-2*|a|)*Real.log T := by sorry

theorem pairFourier_integrated_error (g : ℝ → ℂ) (hg : Continuous g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1)
    (M A B T : ℝ) (hM : ∀ a, ‖g a‖≤M) (hA : 0≤A) (_hB : 0≤B) (hT : 3≤T)
    (hF : ∀ a : ℝ, |a|≤1 →
      |pairNormalizedCorrelation T a-T^(-2*|a|)*Real.log T-(|a|)| ≤
        A*T^(-2*|a|)+B/Real.sqrt (Real.log T)) :
    ‖pairFourierStatistic T g-
      (∫ a : ℝ, g a*(pairFourierPeak (Real.log T) a : ℂ))-
      (∫ a : ℝ, (|a| : ℝ)*g a)‖ ≤
        A*M/Real.log T+B*(∫ a : ℝ, ‖g a‖)/Real.sqrt (Real.log T) := by sorry

theorem pairFourier_named_error_budget :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (g : ℝ → ℂ), Continuous g → HasCompactSupport g →
      Function.support g ⊆ Icc (-1) 1 → ∀ M₀ M₁ : ℝ,
      (∀ a, ‖g a‖≤M₀) → (∀ a : ℝ, ‖g a-g 0‖≤M₁*|a|) → ∀ T : ℝ, 3≤T →
      ‖pairFourierStatistic T g-pairFourierMain g‖ ≤
        (A*M₀+M₁/2)/Real.log T+B*(∫ a : ℝ, ‖g a‖)/Real.sqrt (Real.log T) := by sorry

theorem pairFourier_asymptotic (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1) :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 3≤T →
      ‖pairFourierStatistic T g-pairFourierMain g‖≤C/Real.sqrt (Real.log T) := by sorry

theorem pairFourier_tendsto (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hs : Function.support g ⊆ Icc (-1) 1) :
    Tendsto (fun T : ℝ => pairFourierStatistic T g) atTop (𝓝 (pairFourierMain g)) := by sorry

end
end HigherCorrelations
