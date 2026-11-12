import HigherCorrelations.ApproximateFunctionalMellin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-! UNCONDITIONAL branch and normalization identities for the planned Hankel
contour. These statements do not assert a contour deformation or its error bound. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology

theorem afeHankelLog_exp (z : ℂ) (hz : z ≠ 0) :
    exp (afeHankelLog z) = z := by
  rw [afeHankelLog, exp_add, exp_log (neg_ne_zero.mpr hz), exp_pi_mul_I]
  ring

theorem afeHankelLog_derivative (z : ℂ) (hz : -z ∈ slitPlane) :
    HasDerivAt afeHankelLog z⁻¹ z := by
  have h := ((hasDerivAt_log hz).comp z (hasDerivAt_id z).neg).add_const
    ((Real.pi:ℂ)*I)
  change HasDerivAt (fun w : ℂ => log (-w)+(Real.pi:ℂ)*I) z⁻¹ z
  convert h using 1 <;> simp

theorem afeHankelLog_upper_pole (a : ℝ) (ha : 0 < a) :
    afeHankelLog ((a:ℂ)*I) = (Real.log a:ℂ) + (Real.pi:ℂ)/2*I := by
  unfold afeHankelLog
  rw [show -((a:ℂ)*I) = (a:ℂ)*(-I) by ring,
    log_ofReal_mul ha (neg_ne_zero.mpr I_ne_zero), log_neg_I]
  ring

theorem afeHankelLog_lower_pole (a : ℝ) (ha : 0 < a) :
    afeHankelLog (-((a:ℂ)*I)) = (Real.log a:ℂ) + 3*(Real.pi:ℂ)/2*I := by
  unfold afeHankelLog
  rw [neg_neg, log_ofReal_mul ha I_ne_zero, log_I]
  ring

theorem afeHankelPower_upper_pole (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s ((a:ℂ)*I) =
      (a:ℂ)^(s-1)*exp ((s-1)*(Real.pi:ℂ)/2*I) := by
  rw [afeHankelPower, afeHankelLog_upper_pole a ha, mul_add, exp_add,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← ofReal_log ha.le]
  congr 1 <;> congr 1 <;> ring

theorem afeHankelPower_lower_pole (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s (-((a:ℂ)*I)) =
      (a:ℂ)^(s-1)*exp ((s-1)*3*(Real.pi:ℂ)/2*I) := by
  rw [afeHankelPower, afeHankelLog_lower_pole a ha, mul_add, exp_add,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr ha.ne'), ← ofReal_log ha.le]
  congr 1 <;> congr 1 <;> ring

theorem afe_exp_sine_jump (z : ℂ) :
    exp (2*z*I)-1 = 2*I*exp (z*I)*sin z := by
  have he : exp (z*I)*exp (-z*I) = 1 := by
    rw [← exp_add, show z*I+-z*I=0 by ring, exp_zero]
  have ht : exp (2*z*I) = exp (z*I)*exp (z*I) := by
    rw [← exp_add]; congr 1; ring
  rw [ht, sin]
  linear_combination (norm := ring_nf) he
  simp only [I_sq]
  ring

theorem afeHankelPrefactor_jump (s : ℂ) (hs : s.im ≠ 0) :
    afeHankelPrefactor s * (exp (2*(Real.pi:ℂ)*s*I)-1) * Gamma s = 1 := by
  have havoid (n : ℕ) : s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have havoid' (n : ℕ) : 1-s ≠ -(n:ℂ) := by
    intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hsin : sin ((Real.pi:ℂ)*s) ≠ 0 := by
    intro h
    have hg := Gamma_mul_Gamma_one_sub s
    rw [h, div_zero] at hg
    exact mul_ne_zero (Gamma_ne_zero havoid) (Gamma_ne_zero havoid') hg
  have he : exp (-(Real.pi:ℂ)*s*I)*exp ((Real.pi:ℂ)*s*I) = 1 := by
    rw [← exp_add, show -(Real.pi:ℂ)*s*I+(Real.pi:ℂ)*s*I=0 by ring, exp_zero]
  rw [show 2*(Real.pi:ℂ)*s*I=2*((Real.pi:ℂ)*s)*I by ring, afe_exp_sine_jump]
  unfold afeHankelPrefactor
  calc
    _ = (exp (-(Real.pi:ℂ)*s*I)*exp ((Real.pi:ℂ)*s*I)) *
        (Gamma s * Gamma (1-s)) * sin ((Real.pi:ℂ)*s) / (Real.pi:ℂ) := by
      field_simp
    _ = 1 := by
      rw [he, Gamma_mul_Gamma_one_sub]
      field_simp

theorem afeHankelPower_norm (s z : ℂ) (hz : z ≠ 0) :
    ‖afeHankelPower s z‖ = ‖z‖^(s.re-1) *
      Real.exp (-s.im*(arg (-z)+Real.pi)) := by
  rw [afeHankelPower, norm_exp, afeHankelLog,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz), ← Real.exp_add]
  congr 1
  simp only [mul_re, sub_re, sub_im, one_re, one_im, add_re, add_im,
    log_re, log_im, norm_neg, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem afeHankelPower_derivative (s z : ℂ) (hz : -z ∈ slitPlane) :
    HasDerivAt (afeHankelPower s) ((s-1)*z⁻¹*afeHankelPower s z) z := by
  have h := ((afeHankelLog_derivative z hz).const_mul (s-1)).cexp
  change HasDerivAt (fun w => exp ((s-1)*afeHankelLog w)) _ z
  simpa only [afeHankelPower, mul_comm] using h

theorem afeHankelKernel_residue (s : ℂ) (m : ℕ) (p : ℂ)
    (hp : -p ∈ slitPlane) (he : exp p = 1) :
    residue (afeHankelKernel s m) p = afeHankelPower s p := by
  have hd := (hasDerivAt_exp p).tendsto_slope
  rw [he] at hd
  have hi := hd.inv₀ (by norm_num : (1:ℂ) ≠ 0)
  have hc : ContinuousAt (fun z : ℂ => afeHankelPower s z * exp (-(m:ℂ)*z)) p :=
    (afeHankelPower_derivative s p hp).continuousAt.mul (by fun_prop)
  have hnum := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {p}ᶜ))
  have hep : exp (-(m:ℂ)*p) = 1 := by
    rw [show -(m:ℂ)*p = (m:ℂ)*(-p) by ring, exp_nat_mul, exp_neg, he]
    simp
  apply residue_eq_of_tendsto
  convert hnum.mul hi using 1
  · funext z
    simp only [afeHankelKernel, slope, smul_eq_mul, vsub_eq_sub, he,
      mul_inv_rev, inv_inv]
    ring
  · simp only [← neg_mul, hep, inv_one, mul_one]

theorem afeHankelPrefactor_mellin (s : ℂ) (hs : 1 < s.re) (ht : s.im ≠ 0) (m : ℕ) :
    afeHankelPrefactor s * (exp (2*(Real.pi:ℂ)*s*I)-1) *
      (∫ u : ℝ in Ioi 0, (u:ℂ)^(s-1)*exp (-((m:ℝ)*u:ℝ))/(exp (u:ℂ)-1)) =
      riemannZeta s - afePolynomial s m := by
  rw [afe_mellin_tail s hs m, ← mul_assoc, afeHankelPrefactor_jump s ht, one_mul]

theorem afeHankelPower_pole_pair (s : ℂ) (a : ℝ) (ha : 0 < a) :
    afeHankelPower s ((a:ℂ)*I) + afeHankelPower s (-((a:ℂ)*I)) =
      -2 * exp ((Real.pi:ℂ)*s*I) * sin ((Real.pi:ℂ)*s/2) * (a:ℂ)^(s-1) := by
  rw [afeHankelPower_upper_pole s a ha, afeHankelPower_lower_pole s a ha]
  have he : exp ((s-1)*(Real.pi:ℂ)/2*I) + exp ((s-1)*3*(Real.pi:ℂ)/2*I) =
      2*exp ((s-1)*(Real.pi:ℂ)*I)*cos ((s-1)*(Real.pi:ℂ)/2) := by
    rw [cos]
    have h₁ : exp ((s-1)*(Real.pi:ℂ)*I)*exp ((s-1)*(Real.pi:ℂ)/2*I) =
        exp ((s-1)*3*(Real.pi:ℂ)/2*I) := by
      rw [← exp_add]; congr 1; ring
    have h₂ : exp ((s-1)*(Real.pi:ℂ)*I)*exp (-((s-1)*(Real.pi:ℂ)/2)*I) =
        exp ((s-1)*(Real.pi:ℂ)/2*I) := by
      rw [← exp_add]; congr 1; ring
    linear_combination -h₁ -h₂
  have hc : cos ((s-1)*(Real.pi:ℂ)/2) = sin ((Real.pi:ℂ)*s/2) := by
    rw [show (s-1)*(Real.pi:ℂ)/2 = -((Real.pi:ℂ)/2-(Real.pi:ℂ)*s/2) by ring,
      cos_neg, cos_pi_div_two_sub]
  rw [hc, show (s-1)*(Real.pi:ℂ)*I = (Real.pi:ℂ)*s*I-(Real.pi:ℂ)*I by ring,
    exp_sub_pi_mul_I] at he
  linear_combination (a:ℂ)^(s-1)*he

theorem afeChi_power (s : ℂ) :
    pairChi s = 2*(2*(Real.pi:ℂ))^(s-1)*sin ((Real.pi:ℂ)*s/2)*Gamma (1-s) := by
  have hl : log (2*(Real.pi:ℂ)) = (Real.log 2:ℂ)+(Real.log Real.pi:ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_log (by positivity), Real.log_mul (by norm_num) Real.pi_ne_zero]
    push_cast; rfl
  have he : exp (s*(Real.log 2:ℂ))*exp ((s-1)*(Real.log Real.pi:ℂ)) =
      2*(2*(Real.pi:ℂ))^(s-1) := by
    rw [cpow_def_of_ne_zero (mul_ne_zero (by norm_num)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)), hl]
    conv_rhs => lhs; rw [← exp_log (show (2:ℂ) ≠ 0 by norm_num), ← ofNat_log]
    rw [← exp_add, ← exp_add]
    congr 1; ring
  rw [pairChi, he]

theorem afeHankelKernel_residue_pair (s : ℂ) (m k : ℕ) (hk : 0 < k) :
    afeHankelPrefactor s * (2*(Real.pi:ℂ)*I) *
      (residue (afeHankelKernel s m) ((2*Real.pi*k:ℝ)*I) +
       residue (afeHankelKernel s m) (-((2*Real.pi*k:ℝ)*I))) =
      -pairChi s * (k:ℂ)^(s-1) := by
  have ha : 0 < 2*Real.pi*k := by positivity
  have hu : -((2*Real.pi*k:ℝ)*I) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simp only [neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
      add_zero]
    exact neg_ne_zero.mpr ha.ne'
  have hl : -(-((2*Real.pi*k:ℝ)*I)) ∈ slitPlane := by
    apply mem_slitPlane_iff.mpr
    right
    simpa using ha.ne'
  have hep : exp ((2*Real.pi*k:ℝ)*I) = 1 := by
    convert exp_nat_mul_two_pi_mul_I k using 1
    push_cast; congr 1; ring
  have hem : exp (-((2*Real.pi*k:ℝ)*I)) = 1 := by rw [exp_neg, hep, inv_one]
  rw [afeHankelKernel_residue s m _ hu hep, afeHankelKernel_residue s m _ hl hem,
    afeHankelPower_pole_pair s _ ha]
  have he : exp (-(Real.pi:ℂ)*s*I)*exp ((Real.pi:ℂ)*s*I) = 1 := by
    rw [← exp_add, show -(Real.pi:ℂ)*s*I+(Real.pi:ℂ)*s*I=0 by ring, exp_zero]
  have hp : ((2*Real.pi*k:ℝ):ℂ)^(s-1) =
      (2*(Real.pi:ℂ))^(s-1)*(k:ℂ)^(s-1) := by
    simpa only [ofReal_mul, ofReal_ofNat, ofReal_natCast] using
      mul_cpow_ofReal_nonneg (show (0:ℝ) ≤ 2*Real.pi by positivity)
        (show (0:ℝ) ≤ k by positivity) (s-1)
  rw [hp, afeChi_power, afeHankelPrefactor, div_mul_cancel₀ _ (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)]
  linear_combination -2*Gamma (1-s)*sin ((Real.pi:ℂ)*s/2)*
    (2*(Real.pi:ℂ))^(s-1)*(k:ℂ)^(s-1)*he

end
end HigherCorrelations
