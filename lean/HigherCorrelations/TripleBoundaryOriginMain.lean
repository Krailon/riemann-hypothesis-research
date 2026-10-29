import HigherCorrelations.TripleBoundaryLocalNormalization

/-! UNCONDITIONAL origin-profile leading term with the original log T normalization. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_origin_main_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T u v : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hZ : Real.exp u*Real.exp v ≤ T) :
    ‖(tripleRetainedMain ω T (Real.exp u) (Real.exp v):ℂ)/(Real.log T:ℂ)^3-
      (Real.exp (-(2*(u+v))):ℂ)‖ ≤
      4*(1+Real.log 2)*tripleBoundaryLogConstant/Real.log T := by
  have ht := tripleBoundary_height T hT
  have ht3 := (tripleTestBase_bounds T ht.1).1
  have hq : 1 ≤ Real.log T := by
    rw [ht.2.2.1]
    linarith [ht.2.1,Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  have hq0 : 0 < Real.log T := by linarith
  have hK := tripleBoundaryLogConstant_pos
  have hL : Real.log (2*T+2) ≤ tripleBoundaryLogConstant*Real.log T :=
    ht.2.2.2.trans (mul_le_mul_of_nonneg_left (by
      rw [ht.2.2.1]
      linarith [Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]) hK.le)
  have hμ := tripleSmoothingMean_bounds ω hω
  have hμ0 := hμ.1
  have hqC : (Real.log T:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
  have hd : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hx : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu
  have hy : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
  have hg0 := tripleRetainedG_nonneg _ _ hx hy
  have hg := (tripleBoundary_G_height T _ _ ht3 hx hy hZ).trans
    (mul_le_mul_of_nonneg_left hL (by norm_num : (0:ℝ) ≤ 4))
  have hm : Real.log T+tripleSmoothingMean ω ≤ (1+Real.log 2)*Real.log T := by
    nlinarith [mul_le_mul_of_nonneg_left hq hd]
  have hp := mul_le_mul hm hg hg0 (by positivity : 0 ≤ (1+Real.log 2)*Real.log T)
  have he : (tripleRetainedMain ω T (Real.exp u) (Real.exp v):ℂ)/(Real.log T:ℂ)^3-
      (Real.exp (-(2*(u+v))):ℂ) =
      (((Real.log T+tripleSmoothingMean ω)*tripleRetainedG (Real.exp u) (Real.exp v)/Real.log T^3:ℝ):ℂ) := by
    rw [tripleBoundary_main_exponential,← tripleBoundary_G_exponential]
    push_cast
    field_simp [hqC]
    <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_div_of_nonneg_right hp (pow_nonneg hq0.le 3)).trans_eq
  field_simp [hq0.ne']
  <;> ring

end
end HigherCorrelations
