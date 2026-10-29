import HigherCorrelations.TripleQuadrantIntegration
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! UNCONDITIONAL frequency identity, after verifying absolute integral norms. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrant_frequency_sum (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) (p : ℝ × ℝ) :
    (∑' v : MasterTriple, tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v p) =
      tripleQuadrantAmplitude ψ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by
  by_cases hz : tripleQuadrantAmplitude ψ p=0
  · simp [tripleTestFrequencyTerm,hz]
  obtain ⟨hx,hy,hxy⟩ := tripleQuadrant_scale_range ε T p hT (tripleQuadrantAmplitude_support ψ ε hs hz)
  simp only [tripleTestFrequencyTerm,tsum_mul_left]
  rw [tripleTestToMaster.tsum_eq (fun v => tripleMasterCoefficient ((tripleTestBase T)^p.1)
    ((tripleTestBase T)^p.2) v*tripleMasterKernel ω T v)]
  rw [tripleMaster_kernel_identity ω hω.smooth.continuous (tripleBudgetWeight_support ω hω)
    _ _ _ (tripleTestBase_bounds T hT).1 hx hy]

theorem tripleQuadrant_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) :
    tripleTestStatistic ω (tripleQuadrantAmplitude ψ) T =
      ∫ p, tripleQuadrantAmplitude ψ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) := by
  have h := integral_occurrence_sum volume (tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T)
    (tripleQuadrantFrequencyTerm_integrable ω ψ hψ hc T hT)
    (tripleQuadrant_integralNorm_summable ω hω ψ hψ hc ε T hε hT hs)
  simp_rw [tripleTestFrequencyTerm_integral ω (tripleQuadrantAmplitude ψ) T hT,tripleQuadrant_frequency_sum ω hω ψ ε T hε hT hs] at h
  simpa only [tsum_mul_left,tripleTestStatistic] using h

theorem tripleQuadrant_zero_sum_absolute (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier (tripleQuadrantAmplitude ψ) (tripleTestArguments T v)‖) := by
  have hi := tripleQuadrant_integralNorm_summable ω hω ψ hψ hc ε T hε hT hs
  have h := (evaluated_integrals_summable volume (tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T)
    (tripleQuadrantFrequencyTerm_integrable ω ψ hψ hc T hT) _ hi
    (fun v => norm_integral_le_integral_norm _)).div_const 8
  simp_rw [tripleTestFrequencyTerm_integral ω (tripleQuadrantAmplitude ψ) T hT,norm_mul,Complex.norm_ofNat] at h
  simpa using h

theorem tripleQuadrant_frequency_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) :
    Integrable (fun p => tripleQuadrantAmplitude ψ p*tripleMasterObservable ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) := by
  have hmeas : AEStronglyMeasurable (fun p => tripleQuadrantAmplitude ψ p*tripleMasterObservable ω T
      ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)) := by
    simp_rw [← tripleQuadrant_frequency_sum ω hω ψ ε T hε hT hs]
    exact (AEMeasurable.tsum (fun v =>
      (tripleQuadrantFrequencyTerm_integrable ω ψ hψ hc T hT v).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  obtain ⟨C,hC,hQ,hbound⟩ := tripleMaster_uniform_integralNorm
  let A := (8/3:ℝ)^3*C^3*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3
  apply ((tripleQuadrantAmplitude_integrable ψ hψ.continuous hc).norm.mul_const A).mono' hmeas
  apply Filter.Eventually.of_forall
  intro p
  by_cases hz : tripleQuadrantAmplitude ψ p=0
  · simp [hz]
  obtain ⟨hx,hy,hxy⟩ := tripleQuadrant_scale_range ε T p hT (tripleQuadrantAmplitude_support ψ ε hs hz)
  have hm := tripleMasterObservable_norm_bound C hC.le hQ ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) T _ _ (tripleTestBase_bounds T hT).1 hx hy
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
