import HigherCorrelations.PairContourAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Meromorphic.Basic

/-! UNCONDITIONAL left-line kernel bounds, uniform in the ordinate and left shift. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory

private theorem left_denominator_lower (a y : ℝ) (ha : a ≤ -(3/2:ℝ)) :
    (1+y^2)/4 ≤ ‖((a:ℂ)+(y:ℂ)*I)^2-1‖ := by
  have ha2 : (3/2:ℝ)^2 ≤ a^2 := by nlinarith
  have hs : ((1+y^2)/4)^2 ≤ ‖((a:ℂ)+(y:ℂ)*I)^2-1‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
    nlinarith [sq_nonneg (a^2-1),sq_nonneg (y^2),mul_nonneg (by linarith : 0 ≤ a^2-2) (sq_nonneg y)]
  nlinarith [norm_nonneg (((a:ℂ)+(y:ℂ)*I)^2-1),sq_nonneg y]

theorem pairContourKernel_left_bound (X t v : ℝ) (M : ℕ) :
    ‖pairContourKernel X t (-(2*(M:ℂ)+1)+(v:ℂ)*I)‖ ≤
      8*Real.exp (-(2*(M:ℝ)+3/2)*Real.log X)/(1+(v-t)^2) := by
  have hM := Nat.cast_nonneg (α:=ℝ) M
  have hd := left_denominator_lower (-(2*(M:ℝ)+3/2)) (v-t) (by linarith)
  have he : -(2*(M:ℂ)+1)+(v:ℂ)*I-pairSpectralPoint t =
      (-(2*(M:ℝ)+3/2):ℝ)+(v-t:ℝ)*I := by push_cast; unfold pairSpectralPoint; ring
  have hn : ‖Complex.exp ((Real.log X:ℂ)*(-(2*(M:ℂ)+1)+(v:ℂ)*I-pairSpectralPoint t))‖ =
      Real.exp (-(2*(M:ℝ)+3/2)*Real.log X) := by
    rw [he, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
    ring
  unfold pairContourKernel
  rw [norm_div, norm_mul, hn, he]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < (1+(v-t)^2)/4) hd).trans_eq
  field_simp
  <;> ring

/-- Totalized functions at poles remain measurable; no pole values enter an integral. -/
theorem pairContourIntegrand_measurable (X t : ℝ) : Measurable (pairContourIntegrand X t) := by
  have hζ : Measurable riemannZeta := by
    apply ContinuousOn.measurable_of_countable_compl (s := {1}ᶜ)
    · exact (differentiableOn_riemannZeta).continuousOn
    · simp
  have hk : Measurable (pairContourKernel X t) := by
    unfold pairContourKernel
    fun_prop
  exact ((measurable_deriv riemannZeta).neg.div hζ).mul hk

end
end HigherCorrelations
