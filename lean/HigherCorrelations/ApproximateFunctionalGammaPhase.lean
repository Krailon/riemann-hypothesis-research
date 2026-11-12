import HigherCorrelations.ApproximateFunctionalGamma
import HigherCorrelations.ApproximateFunctionalPhase
import HigherCorrelations.ApproximateFunctionalAlgebra

/-! UNCONDITIONAL vertical-phase error extracted from complex Stirling. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem afeGammaVerticalError_bound (a t : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) (ht : 2 ≤ t) :
    ‖afeGammaVerticalError a t‖ ≤ 9/t := by
  have htp : 0 < t := by linarith
  let w : ℂ := (a:ℂ)-t*I
  let u : ℂ := (a/t:ℝ)*I
  have hu : ‖u‖ = a/t := by
    simp [u, abs_of_nonneg ha, abs_of_pos htp]
  have huhalf : ‖u‖ ≤ 1/2 := by rw [hu]; apply (div_le_iff₀ htp).mpr; linarith
  have hTaylor := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt huhalf (by norm_num))
  have hinv : (1-‖u‖)⁻¹ ≤ 2 := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2)
      (show 1/2 ≤ 1-‖u‖ by linarith)
    simpa using this
  have hR : ‖log (1+u)-u‖ ≤ (a/t)^2 := by
    apply hTaylor.trans
    calc
      _ ≤ ‖u‖^2*2/2 := by gcongr
      _ = _ := by rw [hu]; ring
  have hcoeff : ‖w-1/2‖ ≤ t+1/2 := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hre : (w-1/2).re = a-1/2 := by simp [w]
    have him : (w-1/2).im = -t := by simp [w]
    rw [hre, him]
    rw [abs_of_nonpos (by linarith : a-1/2 ≤ 0), abs_neg, abs_of_pos htp]
    linarith
  have he : (w-1/2)*u-(a:ℂ) = ((a-1/2)*(a/t):ℝ)*I := by
    apply Complex.ext <;> simp [w, u]
    field_simp
    ring
  have hsmall : ‖(w-1/2)*u-(a:ℂ)‖ ≤ (1/2)*(a/t) := by
    rw [he, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_nonpos (by linarith : a-1/2 ≤ 0),
      abs_of_nonneg (div_nonneg ha htp.le)]
    have := mul_le_mul_of_nonneg_right (show -(a-1/2) ≤ 1/2 by linarith)
      (div_nonneg ha htp.le)
    exact this
  have hsplit : (w-1/2)*log (1+u)-(a:ℂ) =
      (w-1/2)*(log (1+u)-u) + ((w-1/2)*u-(a:ℂ)) := by ring
  have hlocal : ‖(w-1/2)*log (1+u)-(a:ℂ)‖ ≤ 1/t := by
    rw [hsplit]
    have htri := norm_add_le ((w-1/2)*(log (1+u)-u)) ((w-1/2)*u-(a:ℂ))
    rw [norm_mul] at htri
    have hmul := mul_le_mul hcoeff hR (norm_nonneg _) (by positivity : 0 ≤ t+1/2)
    have hnum : (t+1/2)*(a/t)^2+(1/2)*(a/t) ≤ 1/t := by
      have hasq : a^2 ≤ 1/4 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hasq (by positivity : 0 ≤ t+1/2)
      have hat := mul_le_mul_of_nonneg_right ha' htp.le
      apply (le_div_iff₀ htp).mpr
      field_simp
      nlinarith
    linarith
  have hw : t ≤ ‖w‖ := by
    have hh := Complex.abs_im_le_norm w
    simpa [w, abs_of_pos htp] using hh
  have hC := afeStirlingCorrection_bound w (by simpa [w] using ha) (ht.trans hw)
  have hC' : ‖afeStirlingCorrection w‖ ≤ 8/t := hC.trans
    (div_le_div_of_nonneg_left (by norm_num) htp hw)
  have htri := norm_add_le ((w-1/2)*log (1+u)-(a:ℂ)) (afeStirlingCorrection w)
  change ‖((w-1/2)*log (1+u)-(a:ℂ))+afeStirlingCorrection w‖ ≤ _
  calc
    _ ≤ 1/t+8/t := htri.trans (add_le_add hlocal hC')
    _ = _ := by ring

theorem afe_log_lower_vertical (a t : ℝ) (ht : 0 < t) :
    log ((a:ℂ)-t*I) = (Real.log t:ℂ) - (Real.pi:ℂ)/2*I +
      log (1+(a/t:ℝ)*I) := by
  let v : ℂ := 1+(a/t:ℝ)*I
  have hv : 0 < v.re := by simp [v]
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have harg := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  have hn : (-I:ℂ) ≠ 0 := by simp
  have hm := Complex.log_mul hn hv0 (show arg (-I) + arg v ∈ Set.Ioc (-Real.pi) Real.pi by
    simp only [arg_neg_I]
    constructor <;> linarith [Real.pi_pos])
  have hm' := Complex.log_mul_ofReal t ht (-I*v) (mul_ne_zero hn hv0)
  have he : (-I*v)*(t:ℂ) = (a:ℂ)-t*I := by
    apply Complex.ext <;> simp [v]
    field_simp
  rw [he, hm, log_neg_I] at hm'
  dsimp only [v] at hm'
  linear_combination hm'

theorem afe_sin_factor (z : ℂ) :
    sin z = exp ((Real.pi:ℂ)/2*I-(Real.log 2:ℂ)) *
      exp (-z*I) * (1-exp (2*z*I)) := by
  have hc : exp ((Real.pi:ℂ)/2*I-(Real.log 2:ℂ)) = I/2 := by
    rw [exp_sub, Complex.exp_pi_div_two_mul_I]
    norm_cast
    rw [Real.exp_log (by norm_num)]
    rfl
  have he : exp (-z*I)*exp (2*z*I) = exp (z*I) := by
    rw [← exp_add]; congr 1; ring
  rw [hc, sin]
  linear_combination (I/2)*he

theorem afePhase_exp_positive (σ t : ℝ) (ht : 0 < t) :
    afePhase σ t = exp ((((1/2-σ)*Real.log (afeHeight t):ℝ):ℂ) +
      ((-t*Real.log (afeHeight t / Real.exp 1)+Real.pi/4:ℝ):ℂ)*I) := by
  rw [afePhase_positive σ ht, Real.rpow_def_of_pos (afeHeight_pos ht.ne'),
    Complex.ofReal_exp, ← exp_add]
  congr 1
  push_cast; ring

theorem afeChi_phase_factor (σ t : ℝ) (hσ : σ ≤ 1) (ht : 2 ≤ t) :
    pairChi (afePoint σ t) = afePhase σ t * exp (afeGammaVerticalError (1-σ) t) *
      (1-exp ((Real.pi:ℂ)*afePoint σ t*I)) := by
  have htp : 0 < t := by linarith
  have hw : t ≤ ‖1-afePoint σ t‖ := by
    have h := Complex.abs_im_le_norm (1-afePoint σ t)
    simpa [afePoint, abs_of_pos htp] using h
  have hg := afeGamma_stirling_closed (1-afePoint σ t)
    (by simp [afePoint]; linarith) (ht.trans hw)
  rw [pairChi, hg, afe_sin_factor, afePhase_exp_positive σ t htp]
  have hsin : 2*((Real.pi:ℂ)*afePoint σ t/2)*I = (Real.pi:ℂ)*afePoint σ t*I := by ring
  rw [hsin]
  have he : afeStirlingMain (1-afePoint σ t) + ((Real.log (2*Real.pi)/2:ℝ):ℂ) +
      afeStirlingCorrection (1-afePoint σ t) +
      (afePoint σ t*(Real.log 2:ℂ) + (afePoint σ t-1)*(Real.log Real.pi:ℂ)) +
      (((Real.pi:ℂ)/2*I-(Real.log 2:ℂ)) + (-((Real.pi:ℂ)*afePoint σ t/2)*I)) =
      (((1/2-σ)*Real.log (afeHeight t):ℝ):ℂ) +
        ((-t*Real.log (afeHeight t / Real.exp 1)+Real.pi/4:ℝ):ℂ)*I +
        afeGammaVerticalError (1-σ) t := by
    have hw' : 1-afePoint σ t = ((1-σ:ℝ):ℂ)-t*I := by simp [afePoint]; ring
    rw [afeStirlingMain, hw', afe_log_lower_vertical (1-σ) t htp]
    unfold afeGammaVerticalError afeHeight
    rw [abs_of_pos htp, Real.log_div (by positivity : t/(2*Real.pi) ≠ 0)
      (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_div htp.ne' (by positivity : 2*Real.pi ≠ 0),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero]
    unfold afePoint
    push_cast
    ring
  have hexp := congrArg exp he
  simp only [exp_add] at hexp
  simp only [exp_add]
  linear_combination (1-exp ((Real.pi:ℂ)*afePoint σ t*I))*hexp

end
end HigherCorrelations
