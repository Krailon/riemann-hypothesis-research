import HigherCorrelations.SignedCoefficientBound
import HigherCorrelations.TripleTestIntegration

/-! UNCONDITIONAL absolute frequency majorants on the full hexagonal support. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem signedFrequencyTerm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖tripleTestFrequencyTerm ω φ T v p‖ ≤
      ‖φ p‖*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  by_cases hz : φ p=0
  · simp [tripleTestFrequencyTerm,hz]
  have hp := hs (subset_tsupport φ hz)
  have hb := (tripleTestBase_bounds T hT).2.1
  have hh := (signed_coefficient_bound _ hb p (tripleTestToMaster v)).trans
    (Real.rpow_le_rpow_of_exponent_le hb.le hp)
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
    (norm_nonneg (tripleMasterKernel ω T (tripleTestToMaster v))))
    (show 0 ≤ ‖φ p‖*8 by positivity)
  simpa only [tripleTestFrequencyTerm,norm_mul,Complex.norm_ofNat,mul_assoc,mul_left_comm,mul_comm] using h

theorem signedFrequencyTerm_integrable (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : Integrable φ) (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T)
    (hs : tsupport φ ⊆ signedMargin ε) (v : MasterTriple) :
    Integrable (tripleTestFrequencyTerm ω φ T v) := by
  have hm : AEStronglyMeasurable (tripleTestFrequencyTerm ω φ T v) := by
    change AEStronglyMeasurable (fun p => φ p*(8*(tripleMasterCoefficient
      ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) (tripleTestToMaster v)*
        tripleMasterKernel ω T (tripleTestToMaster v))))
    simp_rw [tripleTest_phase T hT]
    exact hφ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  exact (hφ.norm.mul_const _).mono' hm
    (Filter.Eventually.of_forall (signedFrequencyTerm_bound ω φ ε T hε hT hs v))

theorem signedFrequencyTerm_integralNorm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : Integrable φ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) (v : MasterTriple) :
    (∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      tripleTestL1 φ*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  have hi := (signedFrequencyTerm_integrable ω φ hφ ε T hε hT hs v).norm
  have hj := hφ.norm
  exact (integral_mono hi (hj.mul_const _) (signedFrequencyTerm_bound ω φ ε T hε hT hs v)).trans_eq
    (by rw [integral_mul_const]; rfl)

theorem signed_integralNorm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ signedMargin ε) :
    Summable (fun v : MasterTriple => ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  have hk := (h ω hω T (tripleTestBase_bounds T hT).1).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 φ)
  exact hb.of_nonneg_of_le (fun v => integral_nonneg (fun _ => norm_nonneg _))
    (signedFrequencyTerm_integralNorm_bound ω φ hφ ε T hε hT hs)

theorem signed_integralNorm_uniform : ∃ A : ℝ, 0 < A ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ →
    ∀ ε T : ℝ, 0 < ε → 2*Real.pi < T → tsupport φ ⊆ signedMargin ε →
    (∑' v : MasterTriple, ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      A*tripleTestL1 φ*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3 := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  refine ⟨A,hA,?_⟩
  intro ω hω φ hφ ε T hε hT hs
  obtain ⟨hk,hbound⟩ := h ω hω T (tripleTestBase_bounds T hT).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 φ)
  have hm := (signed_integralNorm_summable ω hω φ hφ ε T hε hT hs).tsum_le_tsum
    (signedFrequencyTerm_integralNorm_bound ω φ hφ ε T hε hT hs) hb
  simp only [tsum_mul_left,tsum_mul_right] at hm
  rw [tripleTestToMaster.tsum_eq (fun v => ‖tripleMasterKernel ω T v‖)] at hm
  have hp : 0 ≤ tripleTestL1 φ*(tripleTestBase T)^(1-ε) := by
    have ht := (tripleTestBase_bounds T hT).2.1
    unfold tripleTestL1
    positivity
  have hh := mul_le_mul_of_nonneg_right hbound hp
  exact hm.trans (by nlinarith [hh])

end
end HigherCorrelations
