import HigherCorrelations.PairRHSDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-! UNCONDITIONAL. Exact archimedean primitive and uniform logarithmic comparisons. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHS_log_comparison (T : ℝ) (hT : 3 ≤ T) :
    1 ≤ Real.log T ∧ Real.log T ≤ T ∧
    0 ≤ Real.log (T+2)-Real.log T ∧ Real.log (T+2)-Real.log T ≤ 2/T ∧
    Real.log (T+2) ≤ 2*Real.log T := by
  have hT0 : 0 < T := by linarith
  have hq : 1 ≤ Real.log T := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<3) hT
    linarith [Real.log_three_gt_d9]
  have hdiff : 0 ≤ Real.log (T+2)-Real.log T := sub_nonneg.mpr
    (Real.log_le_log hT0 (by linarith))
  have hhi : Real.log (T+2)-Real.log T ≤ 2/T := by
    rw [← Real.log_div (by positivity : T+2 ≠ 0) hT0.ne']
    have h := Real.log_le_sub_one_of_pos (show 0 < (T+2)/T by positivity)
    have he : (T+2)/T-1 = 2/T := by field_simp; ring
    rwa [he] at h
  have ht : 2/T ≤ 1 := (div_le_one hT0).mpr (by linarith)
  exact ⟨hq, (Real.log_le_sub_one_of_pos hT0).trans (by linarith), hdiff, hhi, by linarith⟩

theorem pairRHS_log_square_derivative (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun u : ℝ => (u+2)*(Real.log (u+2)^2-2*Real.log (u+2)+2))
      (Real.log (t+2)^2) t := by
  have hp : t+2 ≠ 0 := by linarith
  have hlog := (Real.hasDerivAt_log hp).comp t ((hasDerivAt_id t).add_const 2)
  convert ((hasDerivAt_id t).add_const 2).mul
    (((hlog.pow 2).sub (hlog.const_mul 2)).add_const 2) using 1 <;>
    (try funext u) <;> dsimp <;> field_simp <;> ring

theorem pairRHS_log_square_integral (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, Real.log (t+2)^2) =
      (T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
      2*(Real.log 2^2-2*Real.log 2+2) := by
  have hc : ContinuousOn (fun t : ℝ => Real.log (t+2)^2) (Set.uIcc 0 T) := by
    apply ContinuousOn.pow
    apply Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const)
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    change t+2 ≠ 0; linarith [ht.1]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => pairRHS_log_square_derivative t (by
      rw [Set.uIcc_of_le hT] at ht; exact ht.1)) hc.intervalIntegrable
  simpa only [zero_add] using he

theorem pairRHSArch_continuous (X T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (pairRHSArch X) (Set.Icc 0 T) := by
  unfold pairRHSArch
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.div_const
  apply Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const)
  intro t ht; change t+2 ≠ 0; linarith [ht.1]

theorem pairRHSArch_square_integral (X T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, ‖pairRHSArch X t‖^2) =
      (1/X^2)*((T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
        2*(Real.log 2^2-2*Real.log 2+2)) := by
  rw [← pairRHS_log_square_integral T hT, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [pairRHSArch,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

/-- The exact primitive gives an absolute uniform error, including X=1. -/
theorem pairRHSArchSquareError_bound (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    |pairRHSArchSquareError X T| ≤ 64*T*Real.log T/X^2 := by
  obtain ⟨hq,hqt,hd,hdhi,hL⟩ := pairRHS_log_comparison T hT
  have hT0 : 0 < T := by linarith
  have hq0 : 0 ≤ Real.log T := by linarith
  have hL0 : 0 ≤ Real.log (T+2) := by linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl2hi : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hdelta : T*(Real.log (T+2)-Real.log T) ≤ 2 :=
    by simpa [mul_comm] using (le_div_iff₀ hT0).mp hdhi
  have hdprod := mul_le_mul hdelta (show Real.log (T+2)+Real.log T ≤ 3*Real.log T by linarith)
    (by positivity : 0 ≤ Real.log (T+2)+Real.log T) (by norm_num : (0:ℝ) ≤ 2)
  have hsquare : Real.log (T+2)^2 ≤ 4*T*Real.log T := by
    have h1 := sq_le_sq₀ hL0 (by positivity : 0 ≤ 2*Real.log T) |>.mpr hL
    have h2 := mul_le_mul_of_nonneg_right hqt hq0
    nlinarith
  have hlinear : (T+2)*Real.log (T+2) ≤ 4*T*Real.log T := by
    calc
      _ ≤ (2*T)*(2*Real.log T) := mul_le_mul (by linarith) hL hL0 (by positivity)
      _ = _ := by ring
  have hbase : T ≤ T*Real.log T := by nlinarith
  have hqbase : Real.log T ≤ T*Real.log T := by nlinarith
  have hc : 0 ≤ Real.log 2^2-2*Real.log 2+2 ∧
      Real.log 2^2-2*Real.log 2+2 ≤ 2 := by
    constructor
    · nlinarith [sq_nonneg (Real.log 2-1)]
    · nlinarith [mul_nonneg hl2 (sub_nonneg.mpr hl2hi)]
  have hdnon := mul_nonneg (show 0 ≤ T by linarith)
    (mul_nonneg hd (show 0 ≤ Real.log (T+2)+Real.log T by positivity))
  have hb : |(T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
      2*(Real.log 2^2-2*Real.log 2+2)-T*Real.log T^2| ≤ 64*T*Real.log T := by
    apply abs_le.mpr
    constructor <;> nlinarith
  unfold pairRHSArchSquareError
  rw [pairRHSArch_square_integral X T (by linarith)]
  have he : 1/X^2*((T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
      2*(Real.log 2^2-2*Real.log 2+2))-T*Real.log T^2/X^2 =
      ((T+2)*(Real.log (T+2)^2-2*Real.log (T+2)+2)-
      2*(Real.log 2^2-2*Real.log 2+2)-T*Real.log T^2)/X^2 := by ring
  rw [he,abs_div,abs_of_nonneg (sq_nonneg X)]
  exact div_le_div_of_nonneg_right hb (sq_nonneg X)

end
end HigherCorrelations
