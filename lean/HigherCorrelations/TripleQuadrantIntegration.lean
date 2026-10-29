import HigherCorrelations.TripleQuadrantGeometry
import HigherCorrelations.TripleTestIntegration

/-! UNCONDITIONAL quadrant frequency majorants. The zero extension is not
assumed smooth; integrability follows by restriction of the ambient test. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleQuadrantFrequencyTerm_integrable (ω : ℝ → ℝ) (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (T : ℝ)
    (hT : 2*Real.pi < T) (v : MasterTriple) :
    Integrable (tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v) := by
  have he : tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v =
      tripleQuadrant.indicator (tripleTestFrequencyTerm ω ψ T v) := by
    funext p
    by_cases hp : p ∈ tripleQuadrant <;> simp [tripleTestFrequencyTerm,tripleQuadrantAmplitude,hp]
  rw [he]
  exact (tripleTestFrequencyTerm_integrable ω ψ hψ hc T hT v).indicator tripleQuadrant_measurable

theorem tripleQuadrantFrequencyTerm_bound (ω : ℝ → ℝ) (ψ : ℝ × ℝ → ℂ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v p‖ ≤
      ‖tripleQuadrantAmplitude ψ p‖*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  by_cases hz : tripleQuadrantAmplitude ψ p=0
  · simp [tripleTestFrequencyTerm,hz]
  have hp := tripleQuadrantAmplitude_support ψ ε hs hz
  obtain ⟨hx,hy,hxy⟩ := tripleQuadrant_scale_range ε T p hT hp
  have hh := (tripleTest_coefficient_bound _ _ hx hy (tripleTestToMaster v)).trans hxy
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
    (norm_nonneg (tripleMasterKernel ω T (tripleTestToMaster v))))
    (show 0 ≤ ‖tripleQuadrantAmplitude ψ p‖*8 by positivity)
  simpa only [tripleTestFrequencyTerm,norm_mul,Complex.norm_ofNat,mul_assoc,mul_left_comm,mul_comm] using h

theorem tripleQuadrantFrequencyTerm_integralNorm_bound (ω : ℝ → ℝ) (ψ : ℝ × ℝ → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) (v : MasterTriple) :
    (∫ p, ‖tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v p‖) ≤
      tripleTestL1 (tripleQuadrantAmplitude ψ)*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  have hi := (tripleQuadrantFrequencyTerm_integrable ω ψ hψ hc T hT v).norm
  have hj := (tripleQuadrantAmplitude_integrable ψ hψ.continuous hc).norm
  exact (integral_mono hi (hj.mul_const _) (tripleQuadrantFrequencyTerm_bound ω ψ ε T hε hT hs v)).trans_eq
    (by rw [integral_mul_const]; rfl)

theorem tripleQuadrant_integralNorm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) :
    Summable (fun v : MasterTriple => ∫ p, ‖tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v p‖) := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  have hk := (h ω hω T (tripleTestBase_bounds T hT).1).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 (tripleQuadrantAmplitude ψ))
  exact hb.of_nonneg_of_le (fun v => integral_nonneg (fun _ => norm_nonneg _))
    (tripleQuadrantFrequencyTerm_integralNorm_bound ω ψ hψ hc ε T hε hT hs)

theorem tripleQuadrant_integralNorm_uniform : ∃ A : ℝ, 0 < A ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (ψ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ ε T : ℝ, 0 < ε → 2*Real.pi < T → (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-ε) →
    (∑' v : MasterTriple, ∫ p, ‖tripleTestFrequencyTerm ω (tripleQuadrantAmplitude ψ) T v p‖) ≤
      A*tripleTestL1 (tripleQuadrantAmplitude ψ)*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3 := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  refine ⟨A,hA,?_⟩
  intro ω hω ψ hψ hc ε T hε hT hs
  obtain ⟨hk,hbound⟩ := h ω hω T (tripleTestBase_bounds T hT).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 (tripleQuadrantAmplitude ψ))
  have hm := (tripleQuadrant_integralNorm_summable ω hω ψ hψ hc ε T hε hT hs).tsum_le_tsum
    (tripleQuadrantFrequencyTerm_integralNorm_bound ω ψ hψ hc ε T hε hT hs) hb
  simp only [tsum_mul_left,tsum_mul_right] at hm
  rw [tripleTestToMaster.tsum_eq (fun v => ‖tripleMasterKernel ω T v‖)] at hm
  have hp : 0 ≤ tripleTestL1 (tripleQuadrantAmplitude ψ)*(tripleTestBase T)^(1-ε) := by
    have ht := (tripleTestBase_bounds T hT).2.1
    unfold tripleTestL1
    positivity
  have hh := mul_le_mul_of_nonneg_right hbound hp
  exact hm.trans (by nlinarith [hh])

end
end HigherCorrelations
