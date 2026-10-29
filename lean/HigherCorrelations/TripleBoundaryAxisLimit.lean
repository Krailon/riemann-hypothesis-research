import HigherCorrelations.TripleBoundaryAxisMain
import HigherCorrelations.TripleMasterAssembly

/-! UNCONDITIONAL axis profiles on compact rectangles, including the transverse
endpoint s=0. The positive longitudinal frequency stays below one. -/
namespace HigherCorrelations
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem tripleBoundary_axis_uniform (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (r₀ r₁ S : ℝ) (hr₀ : 0 < r₀) (hrange : r₀ ≤ r₁) (hr₁ : r₁ < 1) (hS : 0 ≤ S) :
    TendstoUniformlyOn
      (fun T : ℝ => fun p : ℝ × ℝ =>
        tripleMasterObservable ω T ((tripleTestBase T)^p.1) (Real.exp p.2)/(Real.log T:ℂ)^2)
      (fun p => ((p.1*(1+p.2)*Real.exp (-(2*p.2)):ℝ):ℂ)) atTop (Icc r₀ r₁ ×ˢ Icc 0 S) := by
  have hcω : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  obtain ⟨W,hw⟩ := hcω.exists_bound_of_continuous hω.smooth.continuous
  have hW : 0 ≤ W := (norm_nonneg (ω 0)).trans (hw 0)
  have hw' : ∀ u, ω u ≤ W := fun u => (le_abs_self _).trans (by simpa using hw u)
  obtain ⟨C,hC,h⟩ := tripleBoundary_local_square_bound
  let K := tripleBoundaryLogConstant
  let A := C*(1+W+fourierDerivativeL1 ω 1)
  let H₁ := (1+S)*(Real.log (2*Real.pi)+Real.log 2+(1+Real.log 2)*S/2)
  let H₂ := 1+2*(1+Real.log 2)*(1+S)
  let E : ℝ → ℝ := fun T =>
    A*(K^2*(tripleTestBase T)^(-r₀)+K*(1/Real.log T)+
      Real.exp S*((tripleTestBase T)^(-(1-r₁))*Real.log (2*T+2)^4))+
    H₁*(1/Real.log T)+H₂*((tripleTestBase T)^(-(2*r₀))+
      (tripleTestBase T)^(-(2*r₀))*Real.log T)
  have he : Tendsto E atTop (𝓝 0) := by
    have hp0 := tripleBoundary_base_log_decay r₀ hr₀ 0 (by omega)
    have hp1 := tripleBoundary_base_log_decay (2*r₀) (by linarith) 0 (by omega)
    have hp2 := tripleBoundary_base_log_decay (2*r₀) (by linarith) 1 (by omega)
    simp only [pow_zero,mul_one,pow_one] at hp0 hp1 hp2
    have hh := ((((hp0.const_mul (K^2)).add (tripleBoundary_inverse_log_limit.const_mul K)).add
      ((tripleTest_envelope_tendsto (1-r₁) (by linarith)).const_mul (Real.exp S))).const_mul A).add
      (tripleBoundary_inverse_log_limit.const_mul H₁)
    simpa only [mul_zero,add_zero] using hh.add ((hp1.add hp2).const_mul H₂)
  have hzlim : Tendsto (fun T : ℝ => Real.exp S*(tripleTestBase T)^(-(1-r₁))) atTop (𝓝 0) := by
    simpa only [pow_zero,mul_one,mul_zero] using
      (tripleBoundary_base_log_decay (1-r₁) (by linarith) 0 (by omega)).const_mul (Real.exp S)
  have hzsmall : ∀ᶠ T : ℝ in atTop, Real.exp S*(tripleTestBase T)^(-(1-r₁)) < 1 :=
    (tendsto_order.1 hzlim).2 1 zero_lt_one
  apply tripleBoundary_uniform_of_envelope _ _ _ E he
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp 1),hzsmall] with T hT hsmall
  intro p hp
  have ht := tripleBoundary_height T hT
  have ht3 := (tripleTestBase_bounds T ht.1).1
  have ht0 : 0 < T := by linarith
  obtain ⟨hx,hy,hinv,hproduct,hexp⟩ := tripleBoundary_axis_scales T p.1 p.2 r₀ r₁ S ht.1
    hr₀.le hp.1.1 hp.1.2 hp.2.1 hp.2.2
  have hZT : (tripleTestBase T)^p.1*Real.exp p.2 ≤ T :=
    (div_le_one ht0).mp (hproduct.trans hsmall.le)
  have hr := h ω hω W T _ _ hW hw' hT hx hy hZT
  have hm := tripleBoundary_axis_main_bound ω hω T p.1 p.2 S hT
    (hr₀.le.trans hp.1.1) (hp.1.2.trans hr₁.le) hp.2.1 hp.2.2
  have hA : 0 ≤ A := by dsimp [A]; have := fourierDerivativeL1_nonneg ω 1; positivity
  have hK := tripleBoundaryLogConstant_pos
  have hq0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hH₂ : 0 ≤ H₂ := by dsimp [H₂]; have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num); positivity
  have hfirst : K^2/((tripleTestBase T)^p.1*Real.exp p.2) ≤ K^2*(tripleTestBase T)^(-r₀) := by
    convert mul_le_mul_of_nonneg_left hinv (sq_nonneg K) using 1 <;> ring
  have hlast := mul_le_mul_of_nonneg_right hproduct (show 0 ≤ Real.log (2*T+2)^4 by positivity)
  have hr' := hr.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hfirst le_rfl) hlast) hA)
  have hm' := hm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp
    (show 0 ≤ H₂*(1+Real.log T) by positivity)))
  have hh := dist_triangle
    (tripleMasterObservable ω T ((tripleTestBase T)^p.1) (Real.exp p.2)/(Real.log T:ℂ)^2)
    ((tripleRetainedMain ω T ((tripleTestBase T)^p.1) (Real.exp p.2):ℂ)/(Real.log T:ℂ)^2)
    ((p.1*(1+p.2)*Real.exp (-(2*p.2)):ℝ):ℂ)
  simp only [dist_eq_norm,← sub_div] at hh
  rw [← tripleQuadrantRemainder] at hh
  apply hh.trans
  dsimp only [E,A,H₁,H₂,K]
  convert add_le_add hr' hm' using 1 <;> ring

theorem tripleBoundary_exchanged_axis_uniform (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (r₀ r₁ S : ℝ) (hr₀ : 0 < r₀) (hrange : r₀ ≤ r₁) (hr₁ : r₁ < 1) (hS : 0 ≤ S) :
    TendstoUniformlyOn
      (fun T : ℝ => fun p : ℝ × ℝ =>
        tripleMasterObservable ω T (Real.exp p.2) ((tripleTestBase T)^p.1)/(Real.log T:ℂ)^2)
      (fun p => ((p.1*(1+p.2)*Real.exp (-(2*p.2)):ℝ):ℂ)) atTop (Icc r₀ r₁ ×ˢ Icc 0 S) := by
  have he : (fun T : ℝ => fun p : ℝ × ℝ =>
        tripleMasterObservable ω T (Real.exp p.2) ((tripleTestBase T)^p.1)/(Real.log T:ℂ)^2) =
      (fun T : ℝ => fun p : ℝ × ℝ =>
        tripleMasterObservable ω T ((tripleTestBase T)^p.1) (Real.exp p.2)/(Real.log T:ℂ)^2) := by
    funext T p
    rw [tripleMasterObservable_swap]
  rw [he]
  exact tripleBoundary_axis_uniform ω hω r₀ r₁ S hr₀ hrange hr₁ hS

end
end HigherCorrelations
