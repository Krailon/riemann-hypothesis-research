import HigherCorrelations.ReplacementPartialCalculus

/-! UNCONDITIONAL quantitative Fourier decay from coordinate L1 derivatives.
No bounded-strip compactness constant is hidden in the estimate. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped ContDiff

theorem replacementFourier_partial (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : Bool) (u : ℝ × ℝ) :
    complexFourier (replacementPartial j f) ((u.1:ℂ),(u.2:ℂ)) =
      -(2*Real.pi*Complex.I*(if j then u.2 else u.1))*complexFourier f ((u.1:ℂ),(u.2:ℂ)) := by
  let E := fun p : ℝ × ℝ => Complex.exp (2*Real.pi*Complex.I*((u.1:ℂ)*p.1+(u.2:ℂ)*p.2))
  have hE : ContDiff ℝ ∞ E := by
    exact Complex.contDiff_exp.comp (contDiff_const.mul
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))))
  have hd (p : ℝ × ℝ) : fderiv ℝ E p (replacementCoordinate j) =
      (2*Real.pi*Complex.I*(if j then u.2 else u.1))*E p := by
    have h1 := (Complex.ofRealCLM.hasFDerivAt (x := p.1)).comp p (hasFDerivAt_fst : HasFDerivAt Prod.fst _ p)
    have h2 := (Complex.ofRealCLM.hasFDerivAt (x := p.2)).comp p (hasFDerivAt_snd : HasFDerivAt Prod.snd _ p)
    have h := (((h1.const_mul (u.1:ℂ)).add (h2.const_mul (u.2:ℂ))).const_mul
      (2*Real.pi*Complex.I)).cexp
    change (fderiv ℝ (fun p : ℝ × ℝ => Complex.exp
      (2*Real.pi*Complex.I*((u.1:ℂ)*p.1+(u.2:ℂ)*p.2))) p) _ = _
    change HasFDerivAt E _ p at h
    change fderiv ℝ E p _ = _
    rw [h.fderiv]
    cases j <;> simp [replacementCoordinate, E, ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
  have hi1 : Integrable (fun p => fderiv ℝ E p (replacementCoordinate j)*f p) := by
    simp_rw [hd]
    have hh : Integrable (fun p => E p*f p) :=
      (hE.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
    convert hh.const_mul (2*Real.pi*Complex.I*(if j then u.2 else u.1)) using 1
    funext p
    ring
  have hi2 : Integrable (fun p => E p*fderiv ℝ f p (replacementCoordinate j)) :=
    (hE.continuous.mul (replacementPartial_smooth j f hf).continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ _).mul_left)
  have hi3 : Integrable (fun p => E p*f p) :=
    (hE.continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun p _ => (hE.differentiable (by simp)) p) (fun p _ => (hf.differentiable (by simp)) p)
  simp_rw [hd, mul_assoc, integral_const_mul] at h
  unfold complexFourier replacementPartial
  simpa only [E, mul_comm (fderiv ℝ f _ _), mul_comm (f _), neg_mul, mul_assoc] using h

theorem replacementFourier_power (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : Bool) (n : ℕ) (u : ℝ × ℝ) :
    (2*Real.pi*|if j then u.2 else u.1|)^n*‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖ =
      ‖complexFourier (replacementDeriv j n f) ((u.1:ℂ),(u.2:ℂ))‖ := by
  induction n with
  | zero => simp [replacementDeriv]
  | succ n ih =>
    rw [replacementDeriv_succ, replacementFourier_partial _ (replacementDeriv_smooth j n f hf)
      (replacementDeriv_compact j n f hc), norm_mul, norm_neg, ← ih]
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
    ring

theorem replacementFourier_L1 (f : ℝ × ℝ → ℂ) (u : ℝ × ℝ) :
    ‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤  ∫ p, ‖f p‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with p
  simp [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem replacementFourier_decay (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (A : ℝ) (hA : 0 ≤ A)
    (h0 : (∫ p, ‖f p‖) ≤ A)
    (h22 : ∀ j, (∫ p, ‖replacementDeriv j 22 f p‖) ≤ A) (u : ℝ × ℝ) :
    ‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤
      2^22*A/(1+max |u.1| |u.2|)^22 := by
  let r := max |u.1| |u.2|
  have hr : 0 ≤ r := (abs_nonneg _).trans (le_max_left _ _)
  have hbase := (replacementFourier_L1 f u).trans h0
  have hp : r^22*‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤  A := by
    have hcoord (j : Bool) :
        (2*Real.pi*|if j then u.2 else u.1|)^22*‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤  A := by
      rw [replacementFourier_power f hf hc j 22 u]
      exact (replacementFourier_L1 (replacementDeriv j 22 f) u).trans (h22 j)
    have h1 (j : Bool) : |if j then u.2 else u.1|^22*‖complexFourier f ((u.1:ℂ),(u.2:ℂ))‖  ≤  A := by
      apply le_trans _ (hcoord j)
      gcongr
      nlinarith [Real.pi_gt_three, abs_nonneg (if j then u.2 else u.1)]
    by_cases hu : |u.1| ≤ |u.2|
    · simpa [r, max_eq_right hu] using h1 true
    · simpa [r, max_eq_left (le_of_not_ge hu)] using h1 false
  apply (le_div_iff₀ (by positivity : 0 < (1+r)^22)).mpr
  by_cases hsmall : r ≤ 1
  · have hpow : (1+r)^22 ≤ (2:ℝ)^22 := by gcongr; linarith
    nlinarith [mul_le_mul hbase hpow (by positivity : 0 ≤ (1+r)^22) hA]
  · have hpow : (1+r)^22 ≤ (2*r)^22 := by gcongr; linarith
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ (2:ℝ)^22 by positivity)
    have hh' := mul_le_mul_of_nonneg_left hpow (norm_nonneg (complexFourier f ((u.1:ℂ),(u.2:ℂ))))
    rw [mul_pow] at hh'
    nlinarith

end
end HigherCorrelations
