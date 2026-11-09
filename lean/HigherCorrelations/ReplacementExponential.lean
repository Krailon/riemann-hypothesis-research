import HigherCorrelations.ReplacementPartialCalculus

/-! UNCONDITIONAL quadratic exponential remainder and its directional jets. -/
namespace HigherCorrelations
noncomputable section
open scoped ContDiff


theorem replacementExpRemainder_smooth (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    ContDiff ℝ ∞ (replacementExpRemainder L) := by
  unfold replacementExpRemainder
  fun_prop

theorem replacementPartial_exp (j : Bool) (c : ℂ) (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    replacementPartial j (fun p => c*Complex.exp (L p)) =
      fun p => c*L (replacementCoordinate j)*Complex.exp (L p) := by
  funext p
  unfold replacementPartial
  rw [((L.hasFDerivAt (x := p)).cexp.const_mul c).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem replacementExpRemainder_first (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ) :
    replacementDeriv j 1 (replacementExpRemainder L) =
      fun p => L (replacementCoordinate j)*(Complex.exp (L p)-1) := by
  funext p
  change fderiv ℝ (replacementExpRemainder L) p (replacementCoordinate j) = _
  change fderiv ℝ ((fun x => Complex.exp (L x)-1)-(L : (ℝ × ℝ) → ℂ)) p _ = _
  rw [(((L.hasFDerivAt (x := p)).cexp.sub_const 1).sub (L.hasFDerivAt (x := p))).fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem replacementExpRemainder_higher (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ) (n : ℕ) :
    replacementDeriv j (n+2) (replacementExpRemainder L) =
      fun p => (L (replacementCoordinate j))^(n+2)*Complex.exp (L p) := by
  induction n with
  | zero =>
    rw [show (0+2:ℕ)=1+1 by omega, replacementDeriv_succ, replacementExpRemainder_first]
    funext p
    unfold replacementPartial
    rw [(((L.hasFDerivAt (x := p)).cexp.sub_const 1).const_mul (L (replacementCoordinate j))).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega, replacementDeriv_succ, ih, replacementPartial_exp]
    funext p
    simp [pow_succ, mul_assoc]

theorem replacementExpRemainder_jet_bound (j : Bool) (L : (ℝ × ℝ) →L[ℝ] ℂ)
    (p : ℝ × ℝ) (x R : ℝ) (hx : 0 ≤ x) (hL : ‖L p‖ ≤ 2*x)
    (hR : ‖L p‖ ≤ R) (hc : ‖L (replacementCoordinate j)‖ ≤ 2*x)
    (n : ℕ) (hn : n ≤ 22) :
    ‖replacementDeriv j n (replacementExpRemainder L) p‖  ≤
      2^24*x^2*(1+x)^22*Real.exp R := by
  have hex : Real.exp ‖L p‖  ≤  Real.exp R := Real.exp_le_exp.mpr hR
  have hxpow : 1 ≤ (1+x)^22 := one_le_pow₀ (by linarith)
  have hsmall : 4*x^2*Real.exp R  ≤  2^24*x^2*(1+x)^22*Real.exp R := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos R).le
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxpow)]
  rcases n with _|n
  · change ‖Complex.exp (L p)-1-L p‖  ≤  _
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (L p) 2
    norm_num [Finset.sum_range_succ] at h
    have he : Complex.exp (L p)-1-L p = Complex.exp (L p)-(1+L p) := by ring
    rw [he]
    apply (h.trans _).trans hsmall
    calc
      _  ≤  (2*x)^2*Real.exp R := by gcongr
      _ = _ := by ring
  rcases n with _|n
  · rw [show (0+1:ℕ)=1 by rfl, replacementExpRemainder_first, norm_mul]
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (L p) 1
    norm_num at h
    apply (mul_le_mul hc h (norm_nonneg _) (by positivity)).trans
    apply le_trans _ hsmall
    calc
      _  ≤  (2*x)*(2*x*Real.exp R) := by gcongr
      _ = _ := by ring
  · rw [show n+1+1=n+2 by omega, replacementExpRemainder_higher, norm_mul, norm_pow]
    have he := Complex.norm_exp_le_exp_norm (L p)
    have hp : (2*x)^(n+2)  ≤  2^24*x^2*(1+x)^22 := by
      rw [mul_pow, pow_add x n 2]
      have h2 : (2:ℝ)^(n+2) ≤ 2^24 := by apply pow_le_pow_right₀ (by norm_num); omega
      have hxn : x^n  ≤  (1+x)^22 :=
        (pow_le_pow_left₀ hx (by linarith) n).trans (pow_le_pow_right₀ (by linarith) (by omega))
      calc
        _  ≤  2^24*((1+x)^22*x^2) := by gcongr
        _ = _ := by ring
    exact mul_le_mul ((pow_le_pow_left₀ (norm_nonneg _) hc _).trans hp)
      (he.trans hex) (norm_nonneg _) (by positivity)

end
end HigherCorrelations
