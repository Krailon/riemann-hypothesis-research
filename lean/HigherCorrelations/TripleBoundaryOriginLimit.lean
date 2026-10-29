import HigherCorrelations.TripleBoundaryOriginMain
import HigherCorrelations.TripleBoundaryLocalLimits

/-! UNCONDITIONAL origin profile, uniformly on each closed nonnegative rectangle. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 800000 in
theorem tripleBoundary_origin_uniform (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    TendstoUniformlyOn
      (fun T : ℝ => fun p : ℝ × ℝ =>
        tripleMasterObservable ω T (Real.exp p.1) (Real.exp p.2)/(Real.log T:ℂ)^3)
      (fun p => (Real.exp (-(2*(p.1+p.2))):ℂ)) atTop (Icc 0 U ×ˢ Icc 0 V) := by
  have hcω : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  obtain ⟨W,hw⟩ := hcω.exists_bound_of_continuous hω.smooth.continuous
  have hW : 0 ≤ W := (norm_nonneg (ω 0)).trans (hw 0)
  have hw' : ∀ u, ω u ≤ W := fun u => (le_abs_self _).trans (by simpa using hw u)
  obtain ⟨C,hC,h⟩ := tripleBoundary_local_cube_bound
  let K := tripleBoundaryLogConstant
  let A := C*(1+W+fourierDerivativeL1 ω 1)
  let D := 4*(1+Real.log 2)*K
  let E : ℝ → ℝ := fun T =>
    A*((K^2+K)*(1/Real.log T)+Real.exp (U+V)*(Real.log (2*T+2)^4/T))+D*(1/Real.log T)
  have he : Tendsto E atTop (𝓝 0) := by
    have hh := (((tripleBoundary_inverse_log_limit.const_mul (K^2+K)).add
      (tripleBoundary_height_log_decay.const_mul (Real.exp (U+V)))).const_mul A).add
      (tripleBoundary_inverse_log_limit.const_mul D)
    simpa only [mul_zero,add_zero] using hh
  apply tripleBoundary_uniform_of_envelope _ _ _ E he
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp 1),eventually_ge_atTop (Real.exp (U+V))]
    with T hT hmax
  intro p hp
  have hx : 1 ≤ Real.exp p.1 := Real.one_le_exp_iff.mpr hp.1.1
  have hy : 1 ≤ Real.exp p.2 := Real.one_le_exp_iff.mpr hp.2.1
  have hz : Real.exp p.1*Real.exp p.2 ≤ Real.exp (U+V) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add hp.1.2 hp.2.2)
  have hZT := hz.trans hmax
  have hr := h ω hω W T _ _ hW hw' hT hx hy hZT
  have hm := tripleBoundary_origin_main_bound ω hω T p.1 p.2 hT hp.1.1 hp.2.1 hZT
  have ht3 := (tripleTestBase_bounds T (tripleBoundary_height T hT).1).1
  have hP := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hz (by linarith : 0 ≤ T))
    (by positivity : 0 ≤ Real.log (2*T+2)^4)
  have hA : 0 ≤ A := by dsimp [A]; have := fourierDerivativeL1_nonneg ω 1; positivity
  have hr' := hr.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP) hA)
  have hh := dist_triangle
    (tripleMasterObservable ω T (Real.exp p.1) (Real.exp p.2)/(Real.log T:ℂ)^3)
    ((tripleRetainedMain ω T (Real.exp p.1) (Real.exp p.2):ℂ)/(Real.log T:ℂ)^3)
    (Real.exp (-(2*(p.1+p.2))):ℂ)
  simp only [dist_eq_norm,← sub_div] at hh
  rw [← tripleQuadrantRemainder] at hh
  apply hh.trans
  dsimp only [E,A,D,K]
  convert add_le_add hr' hm using 1 <;> ring

end
end HigherCorrelations
