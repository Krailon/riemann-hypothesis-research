import HigherCorrelations.TripleTestIntegration
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! UNCONDITIONAL frequency identity, after verifying absolute integral norms. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleTest_frequency_sum (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T)
    (hs : tsupport φ ⊆ tripleTestMargin ε) (p : ℝ × ℝ) :
    (∑' v : MasterTriple, tripleTestFrequencyTerm ω φ T v p) =
      φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by
  by_cases hz : φ p=0
  · simp [tripleTestFrequencyTerm,hz]
  obtain ⟨hr,hx,hy,hxy,hzt⟩ := tripleTest_scale_range ε T p hε hT (hs (subset_tsupport φ hz))
  simp only [tripleTestFrequencyTerm,tsum_mul_left]
  rw [tripleTestToMaster.tsum_eq (fun v => tripleMasterCoefficient ((tripleTestBase T)^p.1)
    ((tripleTestBase T)^p.2) v*tripleMasterKernel ω T v)]
  rw [tripleMaster_kernel_identity ω hω.smooth.continuous (tripleBudgetWeight_support ω hω)
    _ _ _ (tripleTestBase_bounds T hT).1 (hr.trans hx) (hr.trans hy)]

theorem tripleTest_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    tripleTestStatistic ω φ T =
      ∫ p, φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by
  have h := integral_occurrence_sum volume (tripleTestFrequencyTerm ω φ T)
    (tripleTestFrequencyTerm_integrable ω φ hφ hc T hT)
    (tripleTest_integralNorm_summable ω hω φ hφ hc ε T hε hT hs)
  simp_rw [tripleTestFrequencyTerm_integral ω φ T hT,tripleTest_frequency_sum ω hω φ ε T hε hT hs] at h
  simpa only [tsum_mul_left,tripleTestStatistic] using h

theorem tripleTest_zero_sum_absolute (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier φ (tripleTestArguments T v)‖) := by
  have hi := tripleTest_integralNorm_summable ω hω φ hφ hc ε T hε hT hs
  have h := (evaluated_integrals_summable volume (tripleTestFrequencyTerm ω φ T)
    (tripleTestFrequencyTerm_integrable ω φ hφ hc T hT) _ hi
    (fun v => norm_integral_le_integral_norm _)).div_const 8
  simp_rw [tripleTestFrequencyTerm_integral ω φ T hT,norm_mul,Complex.norm_ofNat] at h
  simpa using h

theorem tripleTest_frequency_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    Integrable (fun p => φ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) := by
  have hmeas : AEStronglyMeasurable (fun p => φ p*tripleMasterObservable ω T
      ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) := by
    simp_rw [← tripleTest_frequency_sum ω hω φ ε T hε hT hs]
    exact (AEMeasurable.tsum (fun v =>
      (tripleTestFrequencyTerm_integrable ω φ hφ hc T hT v).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  obtain ⟨C,hC,hQ,hbound⟩ := tripleMaster_uniform_integralNorm
  let A := (8/3:ℝ)^3*C^3*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3
  apply ((hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc).norm.mul_const A).mono' hmeas
  apply Filter.Eventually.of_forall
  intro p
  by_cases hz : φ p=0
  · simp [hz]
  obtain ⟨hr,hx,hy,hxy,hzt⟩ := tripleTest_scale_range ε T p hε hT (hs (subset_tsupport φ hz))
  have hm := tripleMasterObservable_norm_bound C hC.le hQ ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) T _ _ (tripleTestBase_bounds T hT).1 (hr.trans hx) (hr.trans hy)
  have hmass : (∫ u, |ω u|)=1 := by simpa only [abs_of_nonneg (hω.nonneg _)] using hω.mass
  simp only [tripleMasterL1Bound,hmass,mul_one] at hm
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left (hm.trans ?_) (norm_nonneg _)
  dsimp [A]
  have hL := tripleBudget_height_log T (tripleTestBase_bounds T hT).1
  have hh := mul_le_mul_of_nonneg_left hxy (show 0 ≤ (8/3:ℝ)^3*C^3*Real.log (2*T+2)^3 by positivity)
  nlinarith [hh]

end
end HigherCorrelations
