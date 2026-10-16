import HigherCorrelations.PairMeanDefinitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! UNCONDITIONAL elementary sinc bounds and absolute kernel integrability.
All removable points use Real.sinc's continuous value one at zero. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairMeanSinc_continuous : Continuous pairMeanSinc :=
  Real.continuous_sinc.comp (by fun_prop)

theorem pairMeanSinc_zero : pairMeanSinc 0 = 1 := by simp [pairMeanSinc]

theorem pairMeanSinc_even (u : ℝ) : pairMeanSinc (-u) = pairMeanSinc u := by
  simp [pairMeanSinc, Real.sinc_neg]

theorem pairMeanSinc_abs_le_one (u : ℝ) : |pairMeanSinc u| ≤ 1 :=
  Real.abs_sinc_le_one _

theorem pairMeanSinc_abs_decay (u : ℝ) (hu : u ≠ 0) :
    |pairMeanSinc u| ≤ 1/(Real.pi*|u|) := by
  rw [pairMeanSinc, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hu),
    abs_div, abs_mul, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

theorem pairMeanSinc_sq_bound (u : ℝ) : pairMeanSinc u^2 ≤ 2/(1+u^2) := by
  have hb := pairMeanSinc_abs_le_one u
  have hb2 : pairMeanSinc u^2 ≤ 1 := by nlinarith [sq_abs (pairMeanSinc u), mul_self_le_mul_self (abs_nonneg _) hb]
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases hu : |u| ≤ 1
  · have hu2 : u^2 ≤ 1 := by nlinarith [sq_abs u, abs_nonneg u]
    nlinarith [mul_le_mul hb2 hu2 (sq_nonneg u) (by norm_num : (0:ℝ) ≤ 1)]
  · have hn : u ≠ 0 := by intro he; simp [he] at hu
    have h := pairMeanSinc_abs_decay u hn
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hp : |pairMeanSinc u| ≤ 1/|u| := h.trans
      (div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr hn)
        (by nlinarith [abs_nonneg u]))
    have hp' : |pairMeanSinc u| * |u| ≤ 1 := (le_div_iff₀ (abs_pos.mpr hn)).mp hp
    have hprod : pairMeanSinc u^2*u^2 ≤ 1 := by
      nlinarith [sq_abs (pairMeanSinc u), sq_abs u,
        sq_nonneg (|pairMeanSinc u| * |u|),
        mul_self_le_mul_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hp']
    nlinarith

theorem pairMeanSinc_sq_integrable : Integrable (fun u : ℝ => pairMeanSinc u^2) := by
  apply (integrable_inv_one_add_sq.const_mul 2).mono' (by
    exact (pairMeanSinc_continuous.pow 2).aestronglyMeasurable)
  filter_upwards [] with u
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (pairMeanSinc u)), div_eq_mul_inv] using pairMeanSinc_sq_bound u

theorem pairMeanK_nonneg (u : ℝ) : 0 ≤ pairMeanK u := by unfold pairMeanK; positivity
theorem pairMeanB_nonneg (u : ℝ) : 0 ≤ pairMeanB u := by unfold pairMeanB; positivity

theorem pairMeanK_continuous : Continuous pairMeanK := by
  unfold pairMeanK
  exact continuous_const.mul ((pairMeanSinc_continuous.comp (by fun_prop)).pow 4)

theorem pairMeanB_continuous : Continuous pairMeanB := by
  unfold pairMeanB
  exact ((pairMeanSinc_continuous.comp (by fun_prop)).pow 2).add
    ((pairMeanSinc_continuous.comp (by fun_prop)).pow 2)

theorem pairMeanK_integrable : Integrable pairMeanK := by
  have hs : Integrable (fun u : ℝ => pairMeanSinc (u/2)^2) :=
    pairMeanSinc_sq_integrable.comp_div (by norm_num : (2:ℝ) ≠ 0)
  apply hs.mono' pairMeanK_continuous.aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (pairMeanK_nonneg u)]
  have h := pairMeanSinc_abs_le_one (u/2)
  have h2 : pairMeanSinc (u/2)^2 ≤ 1 := by nlinarith [sq_abs (pairMeanSinc (u/2)), mul_self_le_mul_self (abs_nonneg _) h]
  unfold pairMeanK
  nlinarith [mul_self_le_mul_self (sq_nonneg (pairMeanSinc (u/2))) h2,
    sq_nonneg (pairMeanSinc (u/2))]

theorem pairMeanB_integrable : Integrable pairMeanB := by
  have hs : Integrable (fun u : ℝ => pairMeanSinc (u/2)^2) :=
    pairMeanSinc_sq_integrable.comp_div (by norm_num : (2:ℝ) ≠ 0)
  exact hs.add (hs.comp_sub_right 1)

end
end HigherCorrelations
