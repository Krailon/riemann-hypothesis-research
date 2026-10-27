import HigherCorrelations.TripleTestPhase

/-! UNCONDITIONAL absolute convergence before frequency/zero interchange. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

/-- Unit-scale master majorization bounds the kernel itself, before Fourier tests. -/
theorem tripleTest_kernel_bound : ∃ A : ℝ, 0 < A ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ T : ℝ, 3 ≤ T → Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T v‖) ∧
    8*(∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖) ≤ A*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,hQ,hbound⟩ := tripleMaster_uniform_integralNorm
  refine ⟨(8/3:ℝ)^3*C^3,by positivity,?_⟩
  intro ω hω T hT
  have hs := tripleMaster_kernel_norm_summable ω hω.smooth.continuous (tripleBudgetWeight_support ω hω)
    T 1 1 hT le_rfl le_rfl
  simp only [tripleTest_coefficient_unit,one_mul] at hs
  refine ⟨hs,?_⟩
  have hi := hbound ω hω.smooth.continuous (tripleBudgetWeight_support ω hω) T 1 1 hT le_rfl le_rfl
  have he := tripleMaster_evaluated_norm_summable ω hω.smooth.continuous
    (tripleBudgetWeight_support ω hω) T 1 1 hT le_rfl le_rfl
  have hh := (he.tsum_le_tsum (fun v => norm_integral_le_integral_norm _) hi.1).trans hi.2
  simp only [tripleMaster_integral_eq_kernel ω T 1 1 (by norm_num) (by norm_num),
    tripleTest_coefficient_unit,one_mul,norm_mul,Complex.norm_ofNat,tsum_mul_left] at hh
  simpa [tripleMasterL1Bound,abs_of_nonneg (hω.nonneg _),hω.mass] using hh

theorem tripleTestFrequencyTerm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖tripleTestFrequencyTerm ω φ T v p‖ ≤
      ‖φ p‖*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  by_cases hz : φ p=0
  · simp [tripleTestFrequencyTerm,hz]
  have hp := hs (subset_tsupport φ hz)
  obtain ⟨hr,hx,hy,hxy,hzT⟩ := tripleTest_scale_range ε T p hε hT hp
  have hh := (tripleTest_coefficient_bound _ _ (hr.trans hx) (hr.trans hy) (tripleTestToMaster v)).trans hxy
  have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh
    (norm_nonneg (tripleMasterKernel ω T (tripleTestToMaster v))))
    (show 0 ≤ ‖φ p‖*8 by positivity)
  simpa only [tripleTestFrequencyTerm,norm_mul,Complex.norm_ofNat,mul_assoc,mul_left_comm,mul_comm] using h

theorem tripleTestFrequencyTerm_integralNorm_bound (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (ε T : ℝ)
    (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) (v : MasterTriple) :
    (∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      tripleTestL1 φ*(8*‖tripleMasterKernel ω T (tripleTestToMaster v)‖*(tripleTestBase T)^(1-ε)) := by
  have hi := (tripleTestFrequencyTerm_integrable ω φ hφ hc T hT v).norm
  have hj := (hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc).norm
  exact (integral_mono hi (hj.mul_const _) (tripleTestFrequencyTerm_bound ω φ ε T hε hT hs v)).trans_eq
    (by rw [integral_mul_const]; rfl)

theorem tripleTest_integralNorm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε T : ℝ) (hε : 0 < ε) (hT : 2*Real.pi < T) (hs : tsupport φ ⊆ tripleTestMargin ε) :
    Summable (fun v : MasterTriple => ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  have hk := (h ω hω T (tripleTestBase_bounds T hT).1).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 φ)
  exact hb.of_nonneg_of_le (fun v => integral_nonneg (fun _ => norm_nonneg _))
    (tripleTestFrequencyTerm_integralNorm_bound ω φ hφ hc ε T hε hT hs)

theorem tripleTest_integralNorm_uniform : ∃ A : ℝ, 0 < A ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ ε T : ℝ, 0 < ε → 2*Real.pi < T → tsupport φ ⊆ tripleTestMargin ε →
    (∑' v : MasterTriple, ∫ p, ‖tripleTestFrequencyTerm ω φ T v p‖) ≤
      A*tripleTestL1 φ*(tripleTestBase T)^(1-ε)*Real.log (2*T+2)^3 := by
  obtain ⟨A,hA,h⟩ := tripleTest_kernel_bound
  refine ⟨A,hA,?_⟩
  intro ω hω φ hφ hc ε T hε hT hs
  obtain ⟨hk,hbound⟩ := h ω hω T (tripleTestBase_bounds T hT).1
  have hk' := hk.comp_injective tripleTestToMaster.injective
  have hb := ((hk'.mul_left 8).mul_right ((tripleTestBase T)^(1-ε))).mul_left (tripleTestL1 φ)
  have hm := (tripleTest_integralNorm_summable ω hω φ hφ hc ε T hε hT hs).tsum_le_tsum
    (tripleTestFrequencyTerm_integralNorm_bound ω φ hφ hc ε T hε hT hs) hb
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
