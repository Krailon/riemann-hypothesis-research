import HigherCorrelations.TripleQuadrantNormalization

/-! UNCONDITIONAL quantitative normalization of the origin and axis approximations. -/
namespace HigherCorrelations
noncomputable section

set_option maxHeartbeats 600000 in
theorem tripleQuadrant_weighted_bound (S b c d μ : ℝ)
    (hS : 0 ≤ S) (hb : 1 ≤ b) (hc : 0 ≤ c) (hμ : 0 ≤ μ) (hμd : μ ≤ d)
    (o o₀ z z₀ : ℂ)
    (ho : ‖o-o₀‖ ≤ S/(4*b)) (ho₀ : ‖o₀‖ ≤ S/4)
    (hz : ‖z-z₀‖ ≤ 3*S/(2*b)) (hz₀ : ‖z₀‖ ≤ 3*S/2) :
    ‖(((b+c)^2/b^2:ℝ):ℂ)*o+((1+μ/(b+c):ℝ):ℂ)*z-(o₀+z₀)‖ ≤
      ((1+c)^2+c*(2+c)+6*(1+d)+6*d)/4*S/b := by
  have hb0 : 0 < b := by linarith
  have hd : 0 ≤ d := hμ.trans hμd
  obtain ⟨ha0,ha,ha10,ha1⟩ := tripleQuadrant_origin_ratio b c hb hc
  obtain ⟨hv0,hv,hv10,hv1⟩ := tripleQuadrant_axis_ratio b c d μ hb hc hμ hμd
  have hh := tripleQuadrant_weighted_difference ((b+c)^2/b^2) (1+μ/(b+c)) o o₀ z z₀
  have hv10' : 0 ≤ 1+μ/(b+c)-1 := by linarith
  rw [abs_of_nonneg ha0,abs_of_nonneg ha10,abs_of_nonneg hv0,abs_of_nonneg hv10'] at hh
  have hv1' : 1+μ/(b+c)-1 ≤ d/b := by linarith
  apply hh.trans
  calc
    _ ≤ (1+c)^2*(S/(4*b))+(c*(2+c)/b)*(S/4)+
        (1+d)*(3*S/(2*b))+(d/b)*(3*S/2) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul ha ho (norm_nonneg _) (by positivity))
        (mul_le_mul ha1 ho₀ (norm_nonneg _) (by positivity)))
        (mul_le_mul hv hz (norm_nonneg _) (by positivity)))
        (mul_le_mul hv1' hz₀ (norm_nonneg _) (by positivity))
    _ = _ := by ring

end
end HigherCorrelations
