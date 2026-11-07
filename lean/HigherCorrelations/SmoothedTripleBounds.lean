import HigherCorrelations.SmoothedTripleDefinitions
import HigherCorrelations.MainTermComparisonAssembly

/-! UNCONDITIONAL uniform additive error bounds. Inherited constants are existential. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem smoothedTriple_norm_scale (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) (z : ℂ) :
    ‖smoothedTripleStatistic ω φ T-z‖ = (2/3:ℝ)*‖frozenStatistic ω φ T-(3/2:ℂ)*z‖ := by
  have he : smoothedTripleStatistic ω φ T-z = (2/3:ℂ)*(frozenStatistic ω φ T-(3/2:ℂ)*z) := by
    unfold smoothedTripleStatistic; ring
  rw [he,norm_mul]
  norm_num

theorem smoothedTriple_separate_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      A*smoothedTripleSignedError φ ω M₀ T κ+C*smoothedTripleKernelError φ M₀ M₁ T κ := by
  obtain ⟨A,C,hA,hC,h⟩ := mainTerm_frozen_bound_deriv
  refine ⟨(2/3)*A,(2/3)*C,by positivity,by positivity,?_⟩
  intro ω hω M₀ M₁ hM₀ hM₁ hw hd φ hφ hc κ T hκ hT hs
  rw [smoothedTriple_norm_scale]
  have hh := mul_le_mul_of_nonneg_left (h ω hω M₀ M₁ hM₀ hM₁ hw hd φ hφ hc κ T hκ hT hs)
    (by norm_num : (0:ℝ)≤2/3)
  convert hh using 1 <;> unfold smoothedTripleSignedError smoothedTripleKernelError <;> ring

theorem smoothedTriple_errors_nonneg (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ω : ℝ → ℝ) (M₀ M₁ T κ : ℝ) (hM₀ : 0≤M₀) (hM₁ : 0≤M₁)
    (hT : 2*Real.pi*Real.exp 1≤T) :
    0≤ smoothedTripleSignedError φ ω M₀ T κ ∧ 0≤ smoothedTripleKernelError φ M₀ M₁ T κ := by
  have hd := hφ.continuous_fderiv (by simp)
  have h0 := (signedSup_bounds φ hφ.continuous hc).1
  have h1 := (signedSup_bounds (fun p => fderiv ℝ φ p (1,0))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (1,0))).1
  have h2 := (signedSup_bounds (fun p => fderiv ℝ φ p (0,1))
    (hd.clm_apply continuous_const) (hc.fderiv_apply ℝ (0,1))).1
  have hc1 : 0≤ signedC1 φ := by unfold signedC1; positivity
  have ht := tripleBoundary_height T hT
  have hb := (tripleTestBase_bounds T ht.1).2.1
  have hl := tripleBudget_height_log T (tripleTestBase_bounds T ht.1).1
  have hd1 := fourierDerivativeL1_nonneg ω 1
  have hi : 0≤tripleTestL1 φ := integral_nonneg (fun _ => norm_nonneg _)
  have hbLog : 0≤Real.log (tripleTestBase T) := by linarith [ht.2.1]
  constructor <;> simp only [smoothedTripleSignedError,smoothedTripleKernelError] <;> positivity

theorem smoothedTriple_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ M₀ M₁ : ℝ,
    0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) → (∀ u, |deriv ω u|≤M₁) →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω M₀ T κ+smoothedTripleKernelError φ M₀ M₁ T κ) := by
  obtain ⟨A,C,hA,hC,h⟩ := smoothedTriple_separate_bound
  refine ⟨max A C,lt_of_lt_of_le hA (le_max_left _ _),?_⟩
  intro ω hω M₀ M₁ hM₀ hM₁ hw hd φ hφ hc κ T hκ hT hs
  have hn := smoothedTriple_errors_nonneg φ hφ hc ω M₀ M₁ T κ hM₀ hM₁ hT
  apply (h ω hω M₀ M₁ hM₀ hM₁ hw hd φ hφ hc κ T hκ hT hs).trans
  rw [mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hn.1)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hn.2)

theorem smoothedWeightSup_bounds (ω : ℝ → ℝ) (hw : Continuous ω) (hc : HasCompactSupport ω) :
    0≤ smoothedWeightSup ω ∧ ∀ x, |ω x|≤ smoothedWeightSup ω := by
  have hb := hw.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hh : ∀ x, |ω x|≤ smoothedWeightSup ω := fun x =>
    le_csSup (by simpa only [Real.norm_eq_abs] using hb) (mem_range_self x)
  exact ⟨(abs_nonneg (ω 0)).trans (hh 0),hh⟩

theorem smoothedWeight_derivative_sup (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    (0≤ smoothedWeightSup ω ∧ ∀ x, |ω x|≤ smoothedWeightSup ω) ∧
    (0≤ smoothedWeightSup (deriv ω) ∧ ∀ x, |deriv ω x|≤ smoothedWeightSup (deriv ω)) := by
  have hc : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  exact ⟨smoothedWeightSup_bounds ω hω.smooth.continuous hc,
    smoothedWeightSup_bounds (deriv ω) (hω.smooth.continuous_deriv (by simp)) hc.deriv⟩

theorem smoothedTriple_sup_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ),
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖smoothedTripleStatistic ω φ T-sineBenchmark (mainTermPhysicalTest φ hφ hc)‖ ≤
      C*(smoothedTripleSignedError φ ω (smoothedWeightSup ω) T κ+
        smoothedTripleKernelError φ (smoothedWeightSup ω) (smoothedWeightSup (deriv ω)) T κ) := by
  obtain ⟨C,hC,h⟩ := smoothedTriple_uniform_bound
  refine ⟨C,hC,?_⟩
  intro ω hω φ hφ hc κ T hκ hT hs
  have hb := smoothedWeight_derivative_sup ω hω
  exact h ω hω _ _ hb.1.1 hb.2.1 hb.1.2 hb.2.2 φ hφ hc κ T hκ hT hs

end
end HigherCorrelations
