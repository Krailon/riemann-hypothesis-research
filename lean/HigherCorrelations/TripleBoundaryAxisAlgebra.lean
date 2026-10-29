import HigherCorrelations.TripleBoundaryLocalNormalization

/-! UNCONDITIONAL axis normalization algebra. No limiting exchange is used. -/
namespace HigherCorrelations
noncomputable section

set_option maxHeartbeats 800000 in
theorem tripleBoundary_axis_coefficient (b c μ d : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hμ : 0 ≤ μ) (hμd : μ ≤ d) :
    |(b+c+μ)*b/(b+c)^2-1| ≤ (c+d)/(b+c) := by
  have hq : 0 < b+c := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hd : 0 ≤ d := hμ.trans hμd
  have he : (b+c+μ)*b/(b+c)^2-1 = (μ*b-c*(b+c))/(b+c)^2 := by
    field_simp
    <;> ring
  rw [he,abs_div,abs_of_pos (sq_pos_of_pos hq)]
  apply (div_le_div_of_nonneg_right (abs_sub _ _) (sq_nonneg _)).trans
  rw [abs_of_nonneg (mul_nonneg hμ hb0),abs_of_nonneg (mul_nonneg hc hq.le)]
  have hh : μ*b ≤ d*(b+c) := mul_le_mul hμd (by linarith) hb0 hd
  apply (div_le_div_of_nonneg_right (add_le_add hh le_rfl) (sq_nonneg _)).trans_eq
  field_simp
  <;> ring

set_option maxHeartbeats 800000 in
theorem tripleBoundary_axis_algebra (q b c μ d r s S a e : ℝ)
    (hb : 1 ≤ b) (hc : 0 ≤ c) (hq : q=b+c) (hμ : 0 ≤ μ) (hμd : μ ≤ d)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hsS : s ≤ S)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (he : 0 ≤ e) :
    |(q^3*(e*a)+(q+μ)*((1+s)*(b*r+s/2)*a+(1+b*r)*(s+b*r/2)*e))/q^2-
      r*(1+s)*a| ≤
      (1+S)*(c+d+(1+d)*S/2)/q+(1+2*(1+d)*(1+S))*(1+q)*e := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hd : 0 ≤ d := hμ.trans hμd
  have hS : 0 ≤ S := hs.trans hsS
  have hbq : b ≤ q := by linarith
  have hbr : b*r ≤ q := (mul_le_mul_of_nonneg_left hr1 hb0).trans (by simpa using hbq)
  have hmu : q+μ ≤ (1+d)*q := by nlinarith [mul_le_mul_of_nonneg_left hq1 hd]
  have hratio : (q+μ)/q^2 ≤ (1+d)/q := by
    apply (div_le_div_of_nonneg_right hmu (sq_nonneg q)).trans_eq
    field_simp
  have hcoef : |(q+μ)*b/q^2-1| ≤ (c+d)/q := by
    simpa only [hq] using tripleBoundary_axis_coefficient b c μ d hb hc hμ hμd
  have hsa : (1+s)*a ≤ 1+S :=
    (mul_le_mul (by linarith : 1+s ≤ 1+S) ha1 ha (by positivity)).trans_eq (mul_one _)
  have hra : r*((1+s)*a) ≤ 1+S :=
    (mul_le_mul hr1 hsa (by positivity) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  have h1 : |((q+μ)*b/q^2-1)*r*(1+s)*a| ≤ ((c+d)/q)*(1+S) := by
    rw [show ((q+μ)*b/q^2-1)*r*(1+s)*a=((q+μ)*b/q^2-1)*(r*((1+s)*a)) by ring,
      abs_mul,abs_of_nonneg (by positivity : 0 ≤ r*((1+s)*a))]
    exact mul_le_mul hcoef hra (by positivity) (by positivity)
  have h2 : (q+μ)/q^2*(1+s)*(s/2)*a ≤ ((1+d)/q)*(1+S)*(S/2) := by
    have hh := mul_le_mul (mul_le_mul hratio hsa (by positivity) (by positivity))
      (show s/2 ≤ S/2 by linarith) (by positivity) (by positivity)
    convert hh using 1 <;> ring
  have hreverse : (q+μ)/q^2*(1+b*r)*(s+b*r/2) ≤ 2*(1+d)*(1+S)*(1+q) := by
    have hsq : s+b*r/2 ≤ (1+S)*q := by
      nlinarith [mul_le_mul_of_nonneg_left hq1 hS]
    have hh := mul_le_mul (mul_le_mul hratio (show 1+b*r ≤ 1+q by linarith)
      (by positivity) (by positivity)) hsq (by positivity) (by positivity)
    have hid : ((1+d)/q)*(1+q)*((1+S)*q)=(1+d)*(1+S)*(1+q) := by field_simp <;> ring
    rw [hid] at hh
    nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ 1+d by positivity) (show 0 ≤ 1+S by positivity))
      (show 0 ≤ 1+q by positivity)]
  have hid : (q^3*(e*a)+(q+μ)*((1+s)*(b*r+s/2)*a+(1+b*r)*(s+b*r/2)*e))/q^2-r*(1+s)*a =
      q*e*a+((q+μ)*b/q^2-1)*r*(1+s)*a+
      (q+μ)/q^2*(1+s)*(s/2)*a+(q+μ)/q^2*(1+b*r)*(s+b*r/2)*e := by
    field_simp
    <;> ring
  rw [hid]
  have ha0 : 0 ≤ q*e*a := by positivity
  have ha2 : 0 ≤ (q+μ)/q^2*(1+s)*(s/2)*a := by positivity
  have ha3 : 0 ≤ (q+μ)/q^2*(1+b*r)*(s+b*r/2)*e := by positivity
  calc
    _ ≤ |q*e*a|+|((q+μ)*b/q^2-1)*r*(1+s)*a|+
        |(q+μ)/q^2*(1+s)*(s/2)*a|+|(q+μ)/q^2*(1+b*r)*(s+b*r/2)*e| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ q*e+((c+d)/q)*(1+S)+((1+d)/q)*(1+S)*(S/2)+
        (2*(1+d)*(1+S)*(1+q))*e := by
      rw [abs_of_nonneg ha0,abs_of_nonneg ha2,abs_of_nonneg ha3]
      exact add_le_add (add_le_add (add_le_add
        (by nlinarith [mul_le_mul_of_nonneg_left ha1 (show 0 ≤ q*e by positivity)]) h1) h2)
        (mul_le_mul_of_nonneg_right hreverse he)
    _ = ((1+S)*(c+d+(1+d)*S/2)/q+(1+2*(1+d)*(1+S))*(1+q)*e)-e := by ring
    _ ≤ _ := sub_le_self _ he

end
end HigherCorrelations
