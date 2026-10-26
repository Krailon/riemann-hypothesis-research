import HigherCorrelations.TripleArithmeticGapBounds

/-! UNCONDITIONAL simplification of the arithmetic gap budgets.
The mixed logarithmic factor is written as sqrt(ell_x^3 ell_y^3),
so no convention for a fractional power is implicit. -/
namespace HigherCorrelations
noncomputable section

private theorem log_product_bound (a b : ℝ) (ha : Real.log 2≤a) (hb : Real.log 2≤b) :
    a*b ≤ Real.sqrt (a^3*b^3)/Real.log 2 := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0≤a := hl.le.trans ha
  have hb0 : 0≤b := hl.le.trans hb
  have hab : Real.log 2^2≤a*b := by nlinarith [mul_le_mul ha hb hl.le ha0]
  have hh := mul_le_mul_of_nonneg_right hab (sq_nonneg (a*b))
  have hsq : (Real.log 2*(a*b))^2≤a^3*b^3 := by nlinarith
  exact (le_div_iff₀ hl).mpr (by
    simpa only [mul_comm] using Real.le_sqrt_of_sq_le hsq)

theorem tripleLogGap_mixed_rate (x y : ℝ) (hx : 1≤x) (hy : 1≤y) :
    tripleLogGapBound (tripleLogCoefficient x) (tripleLogCoefficient y) ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (Real.sqrt x*Real.sqrt y)*Real.sqrt (Real.log (2*x)^3*Real.log (2*y)^3) := by
  let a := Real.log (2*x)
  let b := Real.log (2*y)
  have ha : Real.log 2≤a := Real.log_le_log (by norm_num) (by linarith)
  have hb : Real.log 2≤b := Real.log_le_log (by norm_num) (by linarith)
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0≤a := hl.le.trans ha
  have hb0 : 0≤b := hl.le.trans hb
  have hk := (tripleDyadicConstant_pos 3).le
  have hc := triplePrimeMassConstant_pos.le
  have he : Real.sqrt ((tripleDyadicConstant 3*x*a^3)*(tripleDyadicConstant 3*y*b^3)) =
      tripleDyadicConstant 3*Real.sqrt x*Real.sqrt y*Real.sqrt (a^3*b^3) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    simp only [mul_pow,Real.sq_sqrt (by linarith : 0≤x),Real.sq_sqrt (by linarith : 0≤y),
      Real.sq_sqrt (mul_nonneg (pow_nonneg ha0 3) (pow_nonneg hb0 3))]
    ring
  have hm := mul_le_mul_of_nonneg_left (log_product_bound a b ha hb)
    (by positivity : 0≤triplePrimeMassConstant^2*(Real.sqrt x*Real.sqrt y)/Real.log 2)
  have h := tripleLogGap_mixed_budget x y hx hy
  change tripleLogGapBound _ _ ≤ (triplePrimeMassConstant*Real.sqrt x*a)*
    (triplePrimeMassConstant*Real.sqrt y*b)/Real.log 2 +4*Real.sqrt 2*
      Real.sqrt ((tripleDyadicConstant 3*x*a^3)*(tripleDyadicConstant 3*y*b^3)) at h
  rw [he] at h
  apply h.trans
  change _ ≤ (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
    (Real.sqrt x*Real.sqrt y)*Real.sqrt (a^3*b^3)
  convert add_le_add_right hm (4*Real.sqrt 2*(tripleDyadicConstant 3*Real.sqrt x*Real.sqrt y*Real.sqrt (a^3*b^3))) using 1 <;> ring

theorem tripleLogGap_cubic_rate (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) ≤
      (triplePrimeMassConstant^3/Real.log 2^2+4*Real.sqrt 2*Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3))*
        (X*Y)*Real.log (2*(X*Y))^4 := by
  have hx : 0≤X := by linarith
  have hy : 0≤Y := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  let L := Real.log (2*(X*Y))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2≤L := Real.log_le_log (by norm_num) (by linarith)
  have hL0 : 0≤L := hl.le.trans hL
  have hax : 0≤Real.log (2*X) := Real.log_nonneg (by linarith)
  have hay : 0≤Real.log (2*Y) := Real.log_nonneg (by linarith)
  have haxL : Real.log (2*X)≤L := Real.log_le_log (by positivity) (by nlinarith)
  have hayL : Real.log (2*Y)≤L := Real.log_le_log (by positivity) (by nlinarith)
  have hc := triplePrimeMassConstant_pos.le
  have hk3 := (tripleDyadicConstant_pos 3).le
  have hk5 := (tripleDyadicConstant_pos 5).le
  have hs : Real.sqrt X*Real.sqrt Y*Real.sqrt (X*Y)=X*Y := by
    rw [← Real.sqrt_mul hx,Real.mul_self_sqrt (mul_nonneg hx hy)]
  have he : Real.sqrt ((tripleDyadicConstant 5*(X*Y)*L^5)*(tripleDyadicConstant 3*(X*Y)*L^3)) =
      Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3)*(X*Y)*L^4 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    simp only [mul_pow,Real.sq_sqrt (mul_nonneg hk5 hk3)]
    ring
  have hb := tripleLogGap_cubic_budget X Y hX hY
  change _ ≤ _ +4*Real.sqrt 2*Real.sqrt ((tripleDyadicConstant 5*(X*Y)*L^5)*(tripleDyadicConstant 3*(X*Y)*L^3)) at hb
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul haxL hayL hay hL0)
    (by positivity : 0≤triplePrimeMassConstant^3*(X*Y)*L/Real.log 2)
  have hp : L^3≤L^4/Real.log 2 := (le_div_iff₀ hl).mpr (by nlinarith [mul_le_mul_of_nonneg_right hL (pow_nonneg hL0 3)])
  have hm2 := mul_le_mul_of_nonneg_left hp (by positivity : 0≤triplePrimeMassConstant^3*(X*Y)/Real.log 2)
  have ha : ((triplePrimeMassConstant*Real.sqrt X*Real.log (2*X))*
      (triplePrimeMassConstant*Real.sqrt Y*Real.log (2*Y)))*
      (triplePrimeMassConstant*Real.sqrt (X*Y)*L)/Real.log 2 ≤
      triplePrimeMassConstant^3*(X*Y)*L^4/Real.log 2^2 := by
    calc
      _ = triplePrimeMassConstant^3*(Real.sqrt X*Real.sqrt Y*Real.sqrt (X*Y))*L/Real.log 2*
          (Real.log (2*X)*Real.log (2*Y)) := by ring
      _ ≤ triplePrimeMassConstant^3*(X*Y)*L^3/Real.log 2 := by
        rw [hs]; convert hm using 1 <;> ring
      _ ≤ _ := by convert hm2 using 1 <;> ring
  apply hb.trans
  convert add_le_add_right ha (4*Real.sqrt 2*(Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3)*(X*Y)*L^4)) using 1 <;> ring

end
end HigherCorrelations
