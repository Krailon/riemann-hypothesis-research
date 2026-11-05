import HigherCorrelations.ProfileGapBounds

/-! UNCONDITIONAL effective gap bounds, including all horizontal endpoints. -/
namespace HigherCorrelations
noncomputable section

theorem rationalProfile_eq_gap_factors (a b e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    rationalProfile a b e f g = (Real.pi:ℂ)*profileReciprocalSum
      (profileGapFactor (a-b) (e-f)) (profileGapFactor a (e+g)) (profileGapFactor b (f+g)) := by
  have h12 : |e-f|≤1 := (abs_sub e f).trans (by linarith)
  have h13 : |e+g|≤1 := (abs_add_le e g).trans (by linarith)
  have h23 : |f+g|≤1 := (abs_add_le f g).trans (by linarith)
  have e12 : ((a:ℂ)-Complex.I*e)-((b:ℂ)-Complex.I*f)=((a-b:ℝ):ℂ)-Complex.I*((e-f:ℝ):ℂ) := by
    push_cast
    ring
  have e13 : ((a:ℂ)-Complex.I*e)-Complex.I*g=(a:ℂ)-Complex.I*((e+g:ℝ):ℂ) := by push_cast; ring
  have e23 : ((b:ℂ)-Complex.I*f)-Complex.I*g=(b:ℂ)-Complex.I*((f+g:ℝ):ℂ) := by push_cast; ring
  unfold rationalProfile
  rw [rationalKernel_reciprocal ((a:ℂ)-Complex.I*e) ((b:ℂ)-Complex.I*f) (Complex.I*g)
    (by rw [e12]; exact profileGapFactor_denominator_ne (a-b) (e-f) h12)
    (by rw [e13]; exact profileGapFactor_denominator_ne a (e+g) h13)
    (by rw [e23]; exact profileGapFactor_denominator_ne b (f+g) h23)]
  simp only [e12,e13,e23,profileReciprocalSum,profileGapFactor,div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

theorem profileGapFactor_difference_bounded (R x h : ℝ) (hR : 0≤R)
    (hx : |x|≤2*R) (hh : |h|≤1) :
    ‖profileGapFactor x h-profileGapFactor 0 h‖≤(2*R+2)*|x|/9 := by
  apply (profileGapFactor_difference x h hh).trans
  gcongr

theorem rationalProfile_gap_bound (R a b e f g : ℝ) (hR : 0≤R)
    (ha : |a|≤R) (hb : |b|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile a b e f g-rationalProfile 0 0 e f g‖ ≤
      (8*Real.pi*(R+1)/9)*(|a|+|b|) := by
  have h12 : |e-f|≤1 := (abs_sub e f).trans (by linarith)
  have h13 : |e+g|≤1 := (abs_add_le e g).trans (by linarith)
  have h23 : |f+g|≤1 := (abs_add_le f g).trans (by linarith)
  have hab : |a-b|≤2*R := (abs_sub a b).trans (by linarith)
  have h1 := profileGapFactor_difference_bounded R (a-b) (e-f) hR hab h12
  have h2 := profileGapFactor_difference_bounded R a (e+g) hR (by linarith) h13
  have h3 := profileGapFactor_difference_bounded R b (f+g) hR (by linarith) h23
  have hs : ‖profileGapFactor (a-b) (e-f)-profileGapFactor 0 (e-f)‖+
      ‖profileGapFactor a (e+g)-profileGapFactor 0 (e+g)‖+
      ‖profileGapFactor b (f+g)-profileGapFactor 0 (f+g)‖ ≤
        ((4*R+4)/9)*(|a|+|b|) := by
    have ht := mul_le_mul_of_nonneg_left (abs_sub a b) (show 0≤(2*R+2)/9 by positivity)
    linarith
  rw [rationalProfile_eq_gap_factors a b e f g he hf hg,
    rationalProfile_eq_gap_factors 0 0 e f g he hf hg,sub_self,← mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hp := profileReciprocalSum_difference
    (profileGapFactor (a-b) (e-f)) (profileGapFactor a (e+g)) (profileGapFactor b (f+g))
    (profileGapFactor 0 (e-f)) (profileGapFactor 0 (e+g)) (profileGapFactor 0 (f+g))
    (profileGapFactor_norm_bound _ _ h12) (profileGapFactor_norm_bound _ _ h13)
    (profileGapFactor_norm_bound _ _ h13) (profileGapFactor_norm_bound _ _ h23)
  have h := mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left hs (by norm_num))) Real.pi_pos.le
  exact h.trans_eq (by ring)

theorem rationalProfile_scaled_gap_bound (R ℓ u v e f g : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (v/ℓ) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by
  have hℓ0 : 0<ℓ := by linarith
  have ha : |u/ℓ|≤R := by
    rw [abs_div,abs_of_pos hℓ0]
    exact (div_le_self (abs_nonneg u) hℓ).trans hu
  have hb : |v/ℓ|≤R := by
    rw [abs_div,abs_of_pos hℓ0]
    exact (div_le_self (abs_nonneg v) hℓ).trans hv
  apply (rationalProfile_gap_bound R (u/ℓ) (v/ℓ) e f g hR ha hb he hf hg).trans
  rw [abs_div,abs_div,abs_of_pos hℓ0]
  calc
    _ ≤ (8*Real.pi*(R+1)/9)*(R/ℓ+R/ℓ) := by gcongr
    _ = _ := by ring

end
end HigherCorrelations
