import HigherCorrelations.PairLeftKernel
import HigherCorrelations.PairLeftBounds
import HigherCorrelations.PairLogWeight
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! UNCONDITIONAL left contour convergence. First height tends to infinity at fixed
M, X, t; then M tends to infinity, with X > 1 fixed. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory Filter
open scoped Topology

private theorem left_majorant_integrable (C G t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ => (C+G*Real.log (|v|+2)+2*M)/(1+(v-t)^2)) := by
  have h₁ := (integrable_inv_one_add_sq.comp_sub_right t).const_mul (C+2*M)
  have h₂ := (pairLogWeight_integrable t).const_mul G
  convert h₁.add h₂ using 1
  ext v
  simp only [Pi.add_apply]
  ring

private theorem left_majorant (X t C G : ℝ)
    (hC : 0 < C) (hG : 0 < G)
    (hb : ∀ (M : ℕ) (v : ℝ), v ≠ 0 →
      ‖-deriv riemannZeta (-(2*(M:ℂ)+1)+(v:ℂ)*I) /
        riemannZeta (-(2*(M:ℂ)+1)+(v:ℂ)*I)‖ ≤ C+G*Real.log (|v|+2)+2*M)
    (M : ℕ) :
    ∀ᵐ v : ℝ, ‖pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)‖ ≤
      (8*Real.exp (-(2*(M:ℝ)+3/2)*Real.log X))*
        ((C+G*Real.log (|v|+2)+2*M)/(1+(v-t)^2)) := by
  filter_upwards [volume.ae_ne (0:ℝ)] with v hv
  unfold pairContourIntegrand
  rw [norm_mul]
  have hl : 0 ≤ Real.log (|v|+2) := Real.log_nonneg (by have := abs_nonneg v; linarith)
  apply (mul_le_mul (hb M v hv) (pairContourKernel_left_bound X t v M)
    (norm_nonneg _) (by positivity)).trans_eq
  ring

theorem pairContour_left_integrable (X t : ℝ) (M : ℕ) :
    Integrable (fun v : ℝ => pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)) := by
  obtain ⟨C,G,hC,hG,hb⟩ := pairZeta_left_majorant
  apply ((left_majorant_integrable C G t M).const_mul
    (8*Real.exp (-(2*(M:ℝ)+3/2)*Real.log X))).mono'
  · exact ((pairContourIntegrand_measurable X t).comp (by fun_prop)).aestronglyMeasurable
  · exact left_majorant X t C G hC hG hb M

private theorem exp_shift_linear_tendsto (X a b : ℝ) (hX : 1 < X) :
    Tendsto (fun M : ℕ => Real.exp (-(2*(M:ℝ)+3/2)*Real.log X)*(a+b*M))
      atTop (𝓝 0) := by
  have hl : 0 < 2*Real.log X := by have := Real.log_pos hX; positivity
  have h₀ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (2*Real.log X) hl).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2*Real.log X) hl).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop)
  simp only [Real.rpow_zero,one_mul,Real.rpow_one] at h₀ h₁
  have h := ((h₀.const_mul a).add (h₁.const_mul b)).const_mul (Real.exp (-(3/2)*Real.log X))
  simp only [mul_zero,add_zero] at h
  convert h using 1
  ext M
  simp only [Function.comp_apply]
  rw [show -(2*(M:ℝ)+3/2)*Real.log X = -(3/2)*Real.log X + -(2*Real.log X)*(M:ℝ) by ring,
    Real.exp_add]
  ring

theorem pairContour_left_tendsto (X t : ℝ) (hX : 1 < X) :
    Tendsto (fun M : ℕ => ∫ v : ℝ,
      pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)) atTop (𝓝 0) := by
  obtain ⟨C,G,hC,hG,hb⟩ := pairZeta_left_majorant
  let A : ℝ := ∫ v : ℝ, (1+(v-t)^2)⁻¹
  let B : ℝ := ∫ v : ℝ, Real.log (|v|+2)/(1+(v-t)^2)
  have hbound (M : ℕ) : ‖∫ v : ℝ, pairContourIntegrand X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)‖ ≤
      Real.exp (-(2*(M:ℝ)+3/2)*Real.log X)*(8*(C*A+G*B)+16*A*M) := by
    have hi := norm_integral_le_of_norm_le
      ((left_majorant_integrable C G t M).const_mul (8*Real.exp (-(2*(M:ℝ)+3/2)*Real.log X)))
      (left_majorant X t C G hC hG hb M)
    apply hi.trans_eq
    rw [integral_const_mul]
    have he : (fun v : ℝ => (C+G*Real.log (|v|+2)+2*M)/(1+(v-t)^2)) =
        fun v => (C+2*M)*(1+(v-t)^2)⁻¹ + G*(Real.log (|v|+2)/(1+(v-t)^2)) := by
      ext v; ring
    rw [he, integral_add ((integrable_inv_one_add_sq.comp_sub_right t).const_mul _)
      ((pairLogWeight_integrable t).const_mul _), integral_const_mul, integral_const_mul]
    dsimp [A,B]
    ring
  exact squeeze_zero_norm hbound (exp_shift_linear_tendsto X (8*(C*A+G*B)) (16*A) hX)

end
end HigherCorrelations
