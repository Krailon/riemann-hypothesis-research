import HigherCorrelations.SignedIntegration
import HigherCorrelations.SignedMasterIdentity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! UNCONDITIONAL signed frequency identity for integrable compact-margin amplitudes. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem signed_frequency_sum (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (T : ℝ) (hT : 2*Real.pi < T) (p : ℝ × ℝ) :
    (∑' v : MasterTriple, tripleTestFrequencyTerm ω φ T v p) = φ p*signedFrequency ω T p := by
  have hb : 0 < tripleTestBase T := by linarith [(tripleTestBase_bounds T hT).2.1]
  simp only [tripleTestFrequencyTerm,tsum_mul_left]
  rw [tripleTestToMaster.tsum_eq (fun v => tripleMasterCoefficient ((tripleTestBase T)^p.1)
    ((tripleTestBase T)^p.2) v*tripleMasterKernel ω T v)]
  rw [signedFrequency,tripleMaster_positive_kernel_identity ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) _ _ _ (tripleTestBase_bounds T hT).1
    (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos hb _)]

theorem signed_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    tripleTestStatistic ω φ T = ∫ p, φ p*signedFrequency ω T p := by
  have h := integral_occurrence_sum volume (tripleTestFrequencyTerm ω φ T)
    (signedFrequencyTerm_integrable ω φ hφ ε T hε hT hs)
    (signed_integralNorm_summable ω hω φ hφ ε T hε hT hs)
  simp_rw [tripleTestFrequencyTerm_integral ω φ T hT,signed_frequency_sum ω hω φ T hT] at h
  simpa only [tsum_mul_left,tripleTestStatistic] using h

theorem signed_zero_sum_absolute (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier φ (tripleTestArguments T v)‖) := by
  have hi := signed_integralNorm_summable ω hω φ hφ ε T hε hT hs
  have h := (evaluated_integrals_summable volume (tripleTestFrequencyTerm ω φ T)
    (signedFrequencyTerm_integrable ω φ hφ ε T hε hT hs) _ hi
    (fun v => norm_integral_le_integral_norm _)).div_const 8
  simp_rw [tripleTestFrequencyTerm_integral ω φ T hT,norm_mul,Complex.norm_ofNat] at h
  simpa using h

theorem signed_frequency_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Integrable (fun p => φ p*signedFrequency ω T p) := by
  obtain ⟨A,hA,hk⟩ := tripleTest_kernel_bound
  have hk' := ((hk ω hω T (tripleTestBase_bounds T hT).1).1).comp_injective tripleTestToMaster.injective
  have hm : AEStronglyMeasurable (fun p => φ p*signedFrequency ω T p) := by
    simp_rw [← signed_frequency_sum ω hω φ T hT]
    exact (AEMeasurable.tsum (fun v =>
      (signedFrequencyTerm_integrable ω φ hφ ε T hε hT hs v).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  apply (hφ.norm.mul_const (8*(∑' v, ‖tripleMasterKernel ω T (tripleTestToMaster v)‖)*
    (tripleTestBase T)^(1-ε))).mono' hm
  filter_upwards [] with p
  rw [← signed_frequency_sum ω hω φ T hT]
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left ‖φ p‖
  have hbound := signedFrequencyTerm_bound ω φ ε T hε hT hs
  have hn := hb.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => hbound v p)
  have hh := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun v => hbound v p) hb)
  simpa only [tsum_mul_left,tsum_mul_right] using hh

end
end HigherCorrelations
