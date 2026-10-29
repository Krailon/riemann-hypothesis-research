import HigherCorrelations.TripleQuadrantLeadingIntegral

/-! UNCONDITIONAL scalar normalization estimates. All constants precede the height. -/
namespace HigherCorrelations
noncomputable section

theorem tripleQuadrant_origin_ratio (b c : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c) :
    0 ≤ (b+c)^2/b^2 ∧ (b+c)^2/b^2 ≤ (1+c)^2 ∧
    0 ≤ (b+c)^2/b^2-1 ∧ (b+c)^2/b^2-1 ≤ c*(2+c)/b := by
  have hb0 : 0 < b := by linarith
  have hbc : 0 ≤ b+c := by positivity
  have hcb := mul_le_mul_of_nonneg_left hb hc
  have hsq : (b+c)^2 ≤ ((1+c)*b)^2 :=
    pow_le_pow_left₀ hbc (by nlinarith only [hcb]) 2
  refine ⟨by positivity,?_,?_,?_⟩
  · apply (div_le_iff₀ (sq_pos_of_pos hb0)).mpr
    nlinarith only [hsq]
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ (sq_pos_of_pos hb0)).mpr
    nlinarith
  · apply (le_div_iff₀ hb0).mpr
    have he : ((b+c)^2/b^2-1)*b = 2*c+c^2/b := by field_simp; ring
    rw [he]
    have hh : c^2/b ≤ c^2 := (div_le_iff₀ hb0).mpr (by nlinarith [sq_nonneg c])
    nlinarith only [hh]

theorem tripleQuadrant_axis_ratio (b c d μ : ℝ) (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hμ : 0 ≤ μ) (hμd : μ ≤ d) :
    0 ≤ 1+μ/(b+c) ∧ 1+μ/(b+c) ≤ 1+d ∧
    0 ≤ μ/(b+c) ∧ μ/(b+c) ≤ d/b := by
  have hb0 : 0 < b := by linarith
  have hq : 0 < b+c := by positivity
  have hd : 0 ≤ d := hμ.trans hμd
  have hh : μ/(b+c) ≤ d/b := by
    apply div_le_div₀ hd hμd hb0 (by linarith)
  have hd' : d/b ≤ d := (div_le_iff₀ hb0).mpr (by nlinarith)
  exact ⟨by positivity,by linarith,by positivity,hh⟩

theorem tripleQuadrant_weighted_difference (a v : ℝ) (o o₀ z z₀ : ℂ) :
    ‖(a:ℂ)*o+(v:ℂ)*z-(o₀+z₀)‖ ≤
      |a| * ‖o-o₀‖+|a-1| * ‖o₀‖+|v| * ‖z-z₀‖+|v-1| * ‖z₀‖ := by
  have he : (a:ℂ)*o+(v:ℂ)*z-(o₀+z₀) =
      (((a:ℂ)*(o-o₀)+((a-1:ℝ):ℂ)*o₀)+(v:ℂ)*(z-z₀))+((v-1:ℝ):ℂ)*z₀ := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ (‖(a:ℂ)*(o-o₀)‖+‖((a-1:ℝ):ℂ)*o₀‖)+‖(v:ℂ)*(z-z₀)‖+‖((v-1:ℝ):ℂ)*z₀‖ :=
      (norm_add_le _ _).trans (add_le_add norm_add₃_le le_rfl)
    _ = _ := by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]

end
end HigherCorrelations
