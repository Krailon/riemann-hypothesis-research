import HigherCorrelations.PairChiIdentity
import HigherCorrelations.PairDigammaRemainder

/-! UNCONDITIONAL archimedean error, with the explicit constant C_psi=2.
The principal logarithm is used throughout, at every real height including zero. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairReflected_norm_lower (t : ℝ) : 3/2 ≤ ‖2-pairSpectralPoint t‖ := by
  have h := Complex.abs_re_le_norm (2-pairSpectralPoint t)
  norm_num [pairSpectralPoint] at h ⊢
  exact h

theorem pairReflected_norm_comparison (t : ℝ) :
    ‖2-pairSpectralPoint t‖ ≤ |t|+2 ∧ |t|+2 ≤ 2*‖2-pairSpectralPoint t‖ := by
  have hs : ‖2-pairSpectralPoint t‖^2 = 9/4+t^2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, pairSpectralPoint]
    ring
  have hn := norm_nonneg (2-pairSpectralPoint t)
  constructor
  · nlinarith [sq_abs t, abs_nonneg t]
  · nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t|-1),
      pairReflected_norm_lower t]

theorem pairReflected_log_bound (t : ℝ) :
    ‖log (2-pairSpectralPoint t)-(Real.log (|t|+2):ℂ)‖ ≤
      Real.log 2 + Real.pi/2 := by
  have hn : 0 < ‖2-pairSpectralPoint t‖ := lt_of_lt_of_le (by norm_num) (pairReflected_norm_lower t)
  have hc := pairReflected_norm_comparison t
  have hlo : Real.log ‖2-pairSpectralPoint t‖ ≤ Real.log (|t|+2) :=
    Real.log_le_log hn hc.1
  have hhi : Real.log (|t|+2) ≤ Real.log 2 + Real.log ‖2-pairSpectralPoint t‖ := by
    rw [← Real.log_mul (by norm_num) hn.ne']
    exact Real.log_le_log (by positivity) hc.2
  have ha : |arg (2-pairSpectralPoint t)| ≤ Real.pi/2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by norm_num [pairSpectralPoint])
  calc
    _ ≤ |(log (2-pairSpectralPoint t)-(Real.log (|t|+2):ℂ)).re| +
        |(log (2-pairSpectralPoint t)-(Real.log (|t|+2):ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      simp only [Complex.sub_re, Complex.log_re, Complex.ofReal_re,
        Complex.sub_im, Complex.log_im, Complex.ofReal_im, sub_zero,
        abs_of_nonpos (sub_nonpos.mpr hlo)]
      linarith

theorem pairArch_logDeriv_bound (t : ℝ) :
    ‖-deriv pairChi (pairSpectralPoint t-1) / pairChi (pairSpectralPoint t-1) -
      (Real.log (|t|+2):ℂ)‖ ≤ pairArchConstant := by
  have hd : ‖digamma (2-pairSpectralPoint t)-log (2-pairSpectralPoint t)‖ ≤ 4/3 := by
    apply (pairDigamma_remainder_bound _ (by norm_num [pairSpectralPoint])).trans
    have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 2 by norm_num)
      (show (0:ℝ) < 3/2 by norm_num) (pairReflected_norm_lower t)
    norm_num at h
    exact h
  have hp : ‖(Real.pi:ℂ)/2 * cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)‖ = Real.pi/2 := by
    rw [norm_mul, pairChi_cot_norm, mul_one, norm_div]
    simp
  have hl : ‖(Real.log (2*Real.pi):ℂ)‖ = Real.log (2*Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    apply Real.log_nonneg
    linarith [Real.pi_gt_three]
  rw [neg_div, pairChi_logDeriv]
  have he : -((Real.log (2*Real.pi):ℂ)+(Real.pi:ℂ)/2*
      cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)-digamma (2-pairSpectralPoint t)) -
      (Real.log (|t|+2):ℂ) =
      -(Real.log (2*Real.pi):ℂ) - (Real.pi:ℂ)/2 *
        cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2) +
      (digamma (2-pairSpectralPoint t)-log (2-pairSpectralPoint t)) +
      (log (2-pairSpectralPoint t)-(Real.log (|t|+2):ℂ)) := by ring
  rw [he]
  calc
    _ ≤ (‖-(Real.log (2*Real.pi):ℂ)‖ +
        ‖(Real.pi:ℂ)/2*cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2)‖) +
        ‖digamma (2-pairSpectralPoint t)-log (2-pairSpectralPoint t)‖ +
        ‖log (2-pairSpectralPoint t)-(Real.log (|t|+2):ℂ)‖ := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ (Real.log (2*Real.pi)+Real.pi/2)+4/3+(Real.log 2+Real.pi/2) := by
      rw [norm_neg,hl,hp]
      exact add_le_add (add_le_add le_rfl hd) (pairReflected_log_bound t)
    _ = _ := by unfold pairArchConstant; ring

theorem pairArchError_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairArchError (X,t)‖ ≤ pairArchConstant / X := by
  unfold pairArchError
  rw [norm_mul, norm_inv]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < X)]
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left
    (pairArch_logDeriv_bound t) (inv_nonneg.mpr (by linarith : 0 ≤ X))

end
end HigherCorrelations
