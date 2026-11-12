import HigherCorrelations.ApproximateFunctionalHankelContour
import Mathlib.Analysis.MellinTransform

/-! UNCONDITIONAL integrability of the fixed-radius positive rays for every
complex parameter. Constants depend on the positive radius and the real part;
this is not the uniform AFE remainder. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

theorem afe_mellin_kernel_norm (s : ℂ) (m : ℕ) (u : ℝ) (hu : 0 < u) :
    ‖(u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ =
      u^(s.re-1)*Real.exp (-((m:ℝ)*u))/(Real.exp u-1) := by
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hu, norm_exp]
  have hd : ‖exp (u:ℂ)-1‖ = Real.exp u-1 := by
    rw [← ofReal_exp, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))]
  rw [hd]
  simp

theorem afe_mellin_ray_majorant (s : ℂ) (m : ℕ) (r a u : ℝ)
    (hr : 0 < r) (hu : r ≤ u) (ha : s.re ≤ a) :
    ‖(u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ ≤
      r^(s.re-a) *
        ‖(u:ℂ)^((a:ℂ)-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)‖ := by
  have hup : 0 < u := hr.trans_le hu
  rw [afe_mellin_kernel_norm s m u hup, afe_mellin_kernel_norm (a:ℂ) m u hup]
  simp only [ofReal_re]
  have hp : u^(s.re-1) ≤ r^(s.re-a)*u^(a-1) := by
    rw [show s.re-1=(s.re-a)+(a-1) by ring, Real.rpow_add hup]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hr hu (sub_nonpos.mpr ha))
      (Real.rpow_nonneg hup.le _)
  calc
    _ ≤ (r^(s.re-a)*u^(a-1))*Real.exp (-((m:ℝ)*u))/(Real.exp u-1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
        (sub_nonneg.mpr (le_of_lt (Real.one_lt_exp_iff.mpr hup)))
    _ = _ := by ring

theorem afe_mellin_ray_integrable (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ =>
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) (Ioi r) := by
  let a : ℝ := max 2 s.re
  have ha : 1 < (a:ℂ).re := by
    change 1 < max 2 s.re
    linarith [le_max_left (2:ℝ) s.re]
  have hI := (afe_mellin_tail_integrable (a:ℂ) ha m).mono_set
    (Ioi_subset_Ioi hr.le)
  refine Integrable.mono' (hI.norm.const_mul (r^(s.re-a))) ?_ ?_
  · exact ((afe_mellin_kernel_continuous s m).mono
      (Ioi_subset_Ioi hr.le)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact afe_mellin_ray_majorant s m r a u hr (le_of_lt hu) (le_max_right _ _)

theorem afeHankelRayWeight_integrable (m : ℕ) (r : ℝ) (hr : 0 < r) :
    Integrable (afeHankelRayWeight m r) := by
  change Integrable ((Ioi r).indicator (fun u : ℝ =>
    exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)))
  rw [integrable_indicator_iff measurableSet_Ioi]
  simpa only [sub_self, cpow_zero, one_mul] using afe_mellin_ray_integrable 1 m r hr

theorem afeHankelRayWeight_decay (m : ℕ) (r : ℝ) :
    afeHankelRayWeight m r =O[atTop] (fun u : ℝ => Real.exp (-u)) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_gt_atTop r, eventually_ge_atTop (1:ℝ)] with u hur hu
  have hup : 0 < u := by linarith
  simp only [afeHankelRayWeight, indicator_of_mem (show u ∈ Ioi r from hur), norm_div, norm_exp,
    Real.norm_eq_abs, Real.abs_exp]
  have hn : ‖exp (u:ℂ)-1‖ = Real.exp u-1 := by
    rw [← ofReal_exp, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hup))]
  rw [hn]
  change Real.exp (-((m:ℝ)*u))/(Real.exp u-1) ≤ 2*Real.exp (-u)
  have he : 2 ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hd : 0 < Real.exp u-1 := by linarith
  have hm : Real.exp (-((m:ℝ)*u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg m) hup.le))
  calc
    _ ≤ 1/(Real.exp u-1) := div_le_div_of_nonneg_right hm hd.le
    _ ≤ _ := by
      rw [Real.exp_neg]
      apply (div_le_iff₀ hd).mpr
      have hp := Real.exp_pos u
      field_simp
      nlinarith

theorem afeHankelRayWeight_zero_bound (m : ℕ) (r b : ℝ) (hr : 0 < r) :
    afeHankelRayWeight m r =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with u hu
  simp [afeHankelRayWeight, show u ∉ Ioi r from not_lt.mpr hu.le]

theorem afeHankelRayWeight_mellin (s : ℂ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    mellin (afeHankelRayWeight m r) s =
      ∫ u : ℝ in Ioi r, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1) := by
  unfold mellin
  have he : (fun u : ℝ => (u:ℂ)^(s-1) • afeHankelRayWeight m r u) =
      (Ioi r).indicator (fun u : ℝ =>
        (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
    funext u
    by_cases hu : u ∈ Ioi r <;> simp [afeHankelRayWeight, hu, smul_eq_mul, mul_div_assoc]
  rw [he, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hr.le)]

theorem afeHankel_ray_differentiable (m : ℕ) (r : ℝ) (hr : 0 < r) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ in Ioi r,
      (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) := by
  intro s
  have h := mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := s.re-1)
    (s := s) (by norm_num) ((afeHankelRayWeight_integrable m r hr).locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (by simpa only [neg_one_mul] using afeHankelRayWeight_decay m r)
    (afeHankelRayWeight_zero_bound m r (s.re-1) hr) (by linarith)
  have he := funext (fun s => afeHankelRayWeight_mellin s m r hr)
  rw [he] at h
  exact h

end
end HigherCorrelations
