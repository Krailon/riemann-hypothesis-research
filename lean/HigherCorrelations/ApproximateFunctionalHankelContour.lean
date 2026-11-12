import HigherCorrelations.ApproximateFunctionalSmallCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! UNCONDITIONAL local deformation for the initial Hankel contour.
All branch values and orientations are specified. This is not the large-height
saddle deformation required for the approximate functional equation. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology

theorem afeHankelLog_circle (r θ : ℝ) (hr : 0 < r)
    (hθ : 0 < θ) (hθ' : θ ≤ 2*Real.pi) :
    afeHankelLog (circleMap 0 r θ) = (Real.log r:ℂ)+(θ:ℂ)*I := by
  have he : -(circleMap 0 r θ) =
      exp ((Real.log r:ℂ)+((θ:ℂ)-(Real.pi:ℂ))*I) := by
    rw [show (Real.log r:ℂ)+((θ:ℂ)-(Real.pi:ℂ))*I =
      ((Real.log r:ℂ)+(θ:ℂ)*I)-(Real.pi:ℂ)*I by ring, exp_sub_pi_mul_I,
      exp_add, ← ofReal_exp, Real.exp_log hr]
    simp [circleMap]
  rw [afeHankelLog, he, log_exp]
  · ring
  · simp only [add_im, ofReal_im, mul_im, sub_re, sub_im, ofReal_re, I_im, I_re]
    linarith
  · simp only [add_im, ofReal_im, mul_im, sub_re, sub_im, ofReal_re, I_im, I_re]
    linarith

theorem afeHankel_circle_lift (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    (∮ z in C(0,r), afeHankelKernel s m z) =
      I * ∫ θ : ℝ in 0..2*Real.pi, afeHankelLift s m ((Real.log r:ℂ)+(θ:ℂ)*I) := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.two_pi_pos.le
  intro θ hθ
  have he : circleMap 0 r θ = exp ((Real.log r:ℂ)+(θ:ℂ)*I) := by
    rw [exp_add, ← ofReal_exp, Real.exp_log hr]
    simp [circleMap]
  simp only [deriv_circleMap, sub_zero, smul_eq_mul, afeHankelKernel,
    afeHankelPower, afeHankelLog_circle r θ hr hθ.1 hθ.2.le, afeHankelLift]
  rw [he]
  have hx : exp ((Real.log r:ℂ)+(θ:ℂ)*I) *
      exp ((s-1)*((Real.log r:ℂ)+(θ:ℂ)*I)) =
      exp (s*((Real.log r:ℂ)+(θ:ℂ)*I)) := by
    rw [← exp_add]; congr 1; ring
  linear_combination I * exp (-(m:ℂ)*exp ((Real.log r:ℂ)+(θ:ℂ)*I)) /
    (exp (exp ((Real.log r:ℂ)+(θ:ℂ)*I))-1)*hx

theorem afeHankelLift_differentiable (s : ℂ) (m : ℕ) (w : ℂ)
    (hw : Real.exp w.re ≤ 1/2) :
    DifferentiableAt ℂ (afeHankelLift s m) w := by
  have hd : exp (exp w)-1 ≠ 0 := by
    have h := afe_exp_small_denominator (exp w) (by rwa [norm_exp])
    intro he
    rw [he, norm_zero] at h
    have := norm_pos_iff.mpr (exp_ne_zero w)
    linarith
  unfold afeHankelLift
  fun_prop

theorem afeHankelLift_period (s w : ℂ) (m : ℕ) :
    afeHankelLift s m (w+2*(Real.pi:ℂ)*I) =
      exp (2*(Real.pi:ℂ)*s*I)*afeHankelLift s m w := by
  have he : exp (w+2*(Real.pi:ℂ)*I) = exp w := by
    rw [exp_add, exp_two_pi_mul_I, mul_one]
  rw [afeHankelLift, he, mul_add, exp_add, afeHankelLift]
  have hx : s*(2*(Real.pi:ℂ)*I) = 2*(Real.pi:ℂ)*s*I := by ring
  rw [hx]; ring

theorem afeHankelLift_rectangle (s : ℂ) (m : ℕ) (a b : ℝ)
    (hab : a ≤ b) (hb : Real.exp b ≤ 1/2) :
    RectangleIntegral (afeHankelLift s m) (a:ℂ) ((b:ℂ)+2*(Real.pi:ℂ)*I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle (U := {w : ℂ | w.re ≤ b})
  · intro w hw
    exact (afeHankelLift_differentiable s m w
      ((Real.exp_le_exp.mpr hw).trans hb)).differentiableWithinAt
  · intro w hw
    have h : a ≤ w.re ∧ w.re ≤ b := by
      simpa [uIcc_of_le hab] using hw.1
    exact h.2

theorem afe_mellin_kernel_continuous (s : ℂ) (m : ℕ) :
    ContinuousOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi 0) := by
  intro u hu
  have hc : ContinuousAt (fun u : ℝ => (u:ℂ)^(s-1)) u :=
    continuous_ofReal.continuousAt.cpow continuousAt_const (Or.inl hu)
  have hn : exp (u:ℂ)-1 ≠ 0 := by
    rw [← ofReal_exp, ← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_exp_iff.mpr hu))
  exact (hc.mul (by fun_prop) |>.div (by fun_prop) hn).continuousWithinAt

theorem afeHankelLift_real_integral (s : ℂ) (m : ℕ) (a b : ℝ) :
    (∫ v : ℝ in a..b, afeHankelLift s m (v:ℂ)) =
      ∫ u : ℝ in Real.exp a..Real.exp b,
        (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by
  have h := intervalIntegral.integral_deriv_smul_comp'
    (g := fun u : ℝ => (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1))
    (fun v (_ : v ∈ uIcc a b) => Real.hasDerivAt_exp v)
    Real.continuous_exp.continuousOn
    ((afe_mellin_kernel_continuous s m).mono (by
      rintro u ⟨v, hv, rfl⟩; exact Real.exp_pos v))
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v hv
  have he : exp (s*(v:ℂ)) = (Real.exp v:ℂ)*(Real.exp v:ℂ)^(s-1) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos v).ne'),
      ← ofReal_log (Real.exp_pos v).le, Real.log_exp, ofReal_exp, ← exp_add]
    congr 1; ring
  dsimp only [afeHankelLift]
  rw [he]
  simp only [Function.comp_def, ofReal_exp, real_smul, ofReal_mul, ofReal_neg, ofReal_natCast]
  ring

theorem afeHankel_circle_difference (s : ℂ) (m : ℕ) (r R : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/2) :
    (∮ z in C(0,R), afeHankelKernel s m z) -
      (∮ z in C(0,r), afeHankelKernel s m z) =
      (exp (2*(Real.pi:ℂ)*s*I)-1) *
        ∫ u : ℝ in r..R, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by
  have hRp : 0 < R := hr.trans_le hrR
  have h := afeHankelLift_rectangle s m (Real.log r) (Real.log R)
    (Real.log_le_log hr hrR) (by rwa [Real.exp_log hRp])
  norm_num [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul] at h
  push_cast at h
  have ht : (∫ x : ℝ in Real.log r..Real.log R,
      afeHankelLift s m ((x:ℂ)+2*(Real.pi:ℂ)*I)) =
      exp (2*(Real.pi:ℂ)*s*I) *
        ∫ x : ℝ in Real.log r..Real.log R, afeHankelLift s m (x:ℂ) := by
    simp only [afeHankelLift_period, intervalIntegral.integral_const_mul]
  have hi := afeHankelLift_real_integral s m (Real.log r) (Real.log R)
  rw [Real.exp_log hr, Real.exp_log hRp] at hi
  rw [afeHankel_circle_lift s m R hRp, afeHankel_circle_lift s m r hr]
  rw [ht, hi] at h
  linear_combination h

theorem afeHankel_circle_mellin (s : ℂ) (hs : 1 < s.re) (m : ℕ)
    (R : ℝ) (hR : 0 < R) (hR' : R ≤ 1/2) :
    (∮ z in C(0,R), afeHankelKernel s m z) =
      (exp (2*(Real.pi:ℂ)*s*I)-1) *
        ∫ u : ℝ in 0..R, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by
  have hI : IntegrableOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (uIcc 0 R) := by
    rw [uIcc_of_le hR.le, integrableOn_Icc_iff_integrableOn_Ioc (by simp)]
    exact (afe_mellin_tail_integrable s hs m).mono_set Ioc_subset_Ioi_self
  have hmem : ∀ᶠ r : ℝ in 𝓝[>] 0, r ∈ uIcc 0 R := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds] with r hr hr'
    rw [uIcc_of_le hR.le]
    exact ⟨le_of_lt hr, hr'.le⟩
  have hi : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝[uIcc 0 R] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds, hmem⟩
  have hp := ((intervalIntegral.continuousOn_primitive_interval_left hI) 0
    left_mem_uIcc).tendsto.comp hi
  have hl := (afeHankel_circle_tendsto_zero s hs m).const_sub
    (∮ z in C(0,R), afeHankelKernel s m z)
  have he : (fun r : ℝ => (∮ z in C(0,R), afeHankelKernel s m z) -
      (∮ z in C(0,r), afeHankelKernel s m z)) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => (exp (2*(Real.pi:ℂ)*s*I)-1) *
        ∫ u : ℝ in r..R, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
    filter_upwards [self_mem_nhdsWithin, hmem] with r hr hr'
    exact afeHankel_circle_difference s m r R hr ((uIcc_of_le hR.le ▸ hr').2) hR'
  simpa using tendsto_nhds_unique (hl.congr' he)
    (hp.const_mul (exp (2*(Real.pi:ℂ)*s*I)-1))

theorem afeHankel_initial_identity (s : ℂ) (hs : 1 < s.re) (ht : s.im ≠ 0)
    (m : ℕ) (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1/2) :
    riemannZeta s - afePolynomial s m =
      afeHankelPrefactor s * ((∮ z in C(0,r), afeHankelKernel s m z) +
        (exp (2*(Real.pi:ℂ)*s*I)-1) *
          ∫ u : ℝ in Ioi r,
            (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
  have he := intervalIntegral.integral_Ioi_sub_Ioi
    (afe_mellin_tail_integrable s hs m) hr.le
  rw [afeHankel_circle_mellin s hs m r hr hr', ← he, ← mul_add,
    sub_add_cancel, ← mul_assoc, afeHankelPrefactor_mellin s hs ht m]

end
end HigherCorrelations
