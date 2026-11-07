import HigherCorrelations.SmoothedTripleConvergence
import HigherCorrelations.SmoothedTripleBounds
import HigherCorrelations.MainTermComparisonAssembly
import HigherCorrelations.ProfileTransferIdentity

/-! UNCONDITIONAL unit-normalized smoothed triple observable. The exact profile
sum is (2/3) times the frozen statistic; all zero occurrences are retained. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem smoothedTripleStatistic_profile_sum (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    smoothedTripleStatistic ω φ T =
      (16/(3*(T:ℂ)*(Real.log T:ℂ)))*
      ∑' v : MasterTriple, (ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*
        complexFourier φ (tripleTestArguments T v) := by
  rw [smoothedTripleStatistic,frozenStatistic_profile_formula]
  ring

theorem smoothedTripleStatistic_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => smoothedTripleStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  simpa [smoothedTripleStatistic] using
    mainTerm_frozen_normalized_limit ω hω φ hφ hc κ hκ hφs

theorem smoothedTripleStatistic_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => smoothedTripleStatistic ω φ T) atTop
      (𝓝 (sineBenchmark (mainTermPhysicalTest φ hφ hc))) := by
  simpa [smoothedTripleStatistic] using
    mainTerm_frozen_normalized_compact_limit ω hω φ hφ hc hφs

/-- Varying tests and smoothings are allowed when the two inherited error
envelopes tend to zero; the benchmark itself may vary with the test. -/
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
      sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n))‖) l (𝓝 0) := by
  obtain ⟨A,C,hA,hC,bound⟩ := mainTerm_frozen_bound_deriv
  have hweighted : Tendsto (fun n => (2/3:ℝ)*
      (A*smoothedTripleSignedError (φ n) (ω n) (M₀ n) (T n) (κ n)+
       C*smoothedTripleKernelError (φ n) (M₀ n) (M₁ n) (T n) (κ n))) l (𝓝 0) := by
    have h₁ := he₁.const_mul A
    have h₂ := he₂.const_mul C
    have hh := h₁.add h₂
    simpa using hh.const_mul (2/3:ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hweighted
  filter_upwards [hT] with n hn
  have hbound := bound (ω n) (hω n) (M₀ n) (M₁ n) (hM₀ n) (hM₁ n) (hw n) (hd n)
    (φ n) (hφ n) (hc n) (κ n) (T n) (hκ n).1 hn (hs n)
  have hscale : ‖smoothedTripleStatistic (ω n) (φ n) (T n)-
      sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n))‖ =
      (2/3:ℝ)*‖frozenStatistic (ω n) (φ n) (T n)-
      (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n))‖ := by
    rw [smoothedTripleStatistic]
    rw [show (2/3:ℂ)*(frozenStatistic (ω n) (φ n) (T n)) -
      sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n)) =
      (2/3:ℂ)*(frozenStatistic (ω n) (φ n) (T n) -
        (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest (φ n) (hφ n) (hc n))) by ring]
    rw [norm_mul]
    norm_num
  rw [hscale]
  simpa only [smoothedTripleSignedError,smoothedTripleKernelError,mul_assoc] using
    mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 2/3)

theorem smoothedTripleStatistic_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => transferCoefficient T*
      ∑ v ∈ tripleDomain S, smoothedTripleTerm ω φ T v) atTop (𝓝 (smoothedTripleStatistic ω φ T)) := by
  rw [smoothedTripleStatistic_profile_sum]
  exact (smoothedTripleTerm_cutoff ω hω φ hi κ T hT hs).const_mul _

theorem smoothedTripleStatistic_height_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => transferCoefficient T*
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), smoothedTripleTerm ω φ T v)
      atTop (𝓝 (smoothedTripleStatistic ω φ T)) := by
  rw [smoothedTripleStatistic_profile_sum]
  exact (smoothedTripleTerm_height_cutoff ω hω φ hi κ T hT hs).const_mul _

theorem smoothedTripleStatistic_zero_test (ω : ℝ → ℝ) (T : ℝ) :
    smoothedTripleStatistic ω (fun _ => 0) T = 0 := by
  simp [smoothedTripleStatistic,frozenStatistic_zero_test]

/-- Standalone all-occurrence smoothed theorem: absolute convergence and a
uniform additive sine-benchmark estimate with the two named errors. -/
theorem smoothedTriple_theorem : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → κ<1 → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    Summable (fun v : MasterTriple => ‖smoothedTripleTerm ω φ T v‖) ∧
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω (smoothedWeightSup ω) T κ+
        smoothedTripleKernelError φ (smoothedWeightSup ω) (smoothedWeightSup (deriv ω)) T κ) := by
  obtain ⟨C,hC,h⟩ := smoothedTriple_sup_bound
  refine ⟨C,hC,?_⟩
  intro ω hω φ hφ hc κ T hκ hκ1 hT hs
  exact ⟨smoothedTripleTerm_summable ω hω φ
    (hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc) κ T (tripleBoundary_height T hT).1 hs,
    h ω hω φ hφ hc κ T hκ hT hs⟩

end
end HigherCorrelations
