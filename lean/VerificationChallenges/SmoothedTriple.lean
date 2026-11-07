import HigherCorrelations.SmoothedTripleDefinitions
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem smoothedTripleTerm_frozen (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ)
    (hT : T ≠ 0) (v : MasterTriple) :
    smoothedTripleTerm ω φ T v = (T:ℂ)*
      (tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) := by sorry

theorem smoothedTripleTerm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v : MasterTriple => ‖smoothedTripleTerm ω φ T v‖) := by sorry

theorem smoothedTripleTerm_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, smoothedTripleTerm ω φ T v)
      atTop (𝓝 (∑' v : MasterTriple, smoothedTripleTerm ω φ T v)) := by sorry

theorem smoothedTripleTerm_height_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), smoothedTripleTerm ω φ T v)
      atTop (𝓝 (∑' v : MasterTriple, smoothedTripleTerm ω φ T v)) := by sorry

theorem smoothedTripleTerm_profile (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : MasterTriple) :
    smoothedTripleTerm ω φ T v = (ω (occurrenceOrdinate (v 0)/T):ℂ)*
      rationalProfile (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 0))
        (occurrenceOrdinate (v 2)-occurrenceOrdinate (v 0))
        (occurrenceDisplacement (v 1)) (occurrenceDisplacement (v 2)) (occurrenceDisplacement (v 0))*
      complexFourier φ (complexPair (actualGaps (meanSpacing T) v) (actualShifts (meanSpacing T) v)) := by sorry

theorem smoothedTriple_norm_scale (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) (z : ℂ) :
    ‖smoothedTripleStatistic ω φ T-z‖ = (2/3:ℝ)*‖frozenStatistic ω φ T-(3/2:ℂ)*z‖ := by sorry

theorem smoothedTriple_separate_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*smoothedTripleSignedError φ ω M₀ T κ+C*smoothedTripleKernelError φ M₀ M₁ T κ := by sorry

theorem smoothedTriple_errors_nonneg (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ω : ℝ → ℝ) (M₀ M₁ T κ : ℝ) (hM₀ : 0≤M₀) (hM₁ : 0≤M₁)
    (hT : 2*Real.pi*Real.exp 1≤T) :
    0≤ smoothedTripleSignedError φ ω M₀ T κ ∧ 0≤ smoothedTripleKernelError φ M₀ M₁ T κ := by sorry

theorem smoothedTriple_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω M₀ T κ+smoothedTripleKernelError φ M₀ M₁ T κ) := by sorry

theorem smoothedWeightSup_bounds (ω : ℝ → ℝ) (hw : Continuous ω) (hc : HasCompactSupport ω) :
    0≤ smoothedWeightSup ω ∧ ∀ x, |ω x|≤ smoothedWeightSup ω := by sorry

theorem smoothedWeight_derivative_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    (0≤ smoothedWeightSup ω ∧ ∀ x, |ω x|≤ smoothedWeightSup ω) ∧
    (0≤ smoothedWeightSup (deriv ω) ∧ ∀ x, |deriv ω x|≤ smoothedWeightSup (deriv ω)) := by sorry

theorem smoothedTriple_sup_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω (smoothedWeightSup ω) T κ+
        smoothedTripleKernelError φ (smoothedWeightSup ω) (smoothedWeightSup (deriv ω)) T κ) := by sorry

theorem smoothedTripleStatistic_profile_sum (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    smoothedTripleStatistic ω φ T =
      (16/(3*(T:ℂ)*(Real.log T:ℂ)))*
      ∑' v : MasterTriple, (ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*
        complexFourier φ (tripleTestArguments T v) := by sorry

theorem smoothedTripleStatistic_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => smoothedTripleStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem smoothedTripleStatistic_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => smoothedTripleStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by sorry

theorem smoothedTripleStatistic_varying_error
    {ι : Type*} {l : Filter ι}
    (T : ι → ℝ) (ω : ι → ℝ → ℝ) (hω : ∀ n, TripleBudgetWeight (ω n))
    (M₀ M₁ κ : ι → ℝ) (φ : ι → ℝ × ℝ → ℂ)
    (hφ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) (hc : ∀ n, HasCompactSupport (φ n))
    (hM₀ : ∀ n, 0 ≤ M₀ n) (hw : ∀ n x, |ω n x| ≤ M₀ n)
    (hM₁ : ∀ n, 0 ≤ M₁ n) (hd : ∀ n x, |deriv (ω n) x| ≤ M₁ n)
    (hκ : ∀ n, 0 < κ n ∧ κ n < 1)
    (hs : ∀ n, tsupport (φ n) ⊆ signedMargin (κ n))
    (hT : ∀ᶠ n in l, 2*Real.pi*Real.exp 1 ≤ T n)
    (he₁ : Tendsto (fun n => smoothedTripleSignedError (φ n) (ω n) (M₀ n) (T n) (κ n)) l (𝓝 0))
    (he₂ : Tendsto (fun n => smoothedTripleKernelError (φ n) (M₀ n) (M₁ n) (T n) (κ n)) l (𝓝 0)) :
    Tendsto (fun n => ‖smoothedTripleStatistic (ω n) (φ n) (T n)-
      sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n))‖) l (𝓝 0) := by sorry

theorem smoothedTripleStatistic_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => transferCoefficient T*
      ∑ v ∈ tripleDomain S, smoothedTripleTerm ω φ T v) atTop (𝓝 (smoothedTripleStatistic ω φ T)) := by sorry

theorem smoothedTripleStatistic_height_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => transferCoefficient T*
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), smoothedTripleTerm ω φ T v)
      atTop (𝓝 (smoothedTripleStatistic ω φ T)) := by sorry

theorem smoothedTripleStatistic_zero_test (ω : ℝ → ℝ) (T : ℝ) :
    smoothedTripleStatistic ω (fun _ => 0) T = 0 := by sorry

theorem smoothedTriple_theorem : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → κ<1 → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    Summable (fun v : MasterTriple => ‖smoothedTripleTerm ω φ T v‖) ∧
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω (smoothedWeightSup ω) T κ+
        smoothedTripleKernelError φ (smoothedWeightSup ω) (smoothedWeightSup (deriv ω)) T κ) := by sorry

end
end HigherCorrelations
