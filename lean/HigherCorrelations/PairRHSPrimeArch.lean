import HigherCorrelations.PairRHSPrimeWeight
import HigherCorrelations.PairRHSOscillation
import HigherCorrelations.PairRHSContinuity

/-! UNCONDITIONAL. Absolute interchange followed by oscillatory cancellation. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem pairRHS_integral_tsum {f : ℕ → ℝ → ℂ} (b : ℕ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hb : Summable b) (hb0 : ∀ n, 0 ≤ b n)
    (hf : ∀ n, ContinuousOn (f n) (Set.uIcc 0 T))
    (hbound : ∀ n t, t ∈ Set.Icc 0 T → ‖f n t‖ ≤ b n) :
    (∫ t in (0:ℝ)..T, ∑' n, f n t) = ∑' n, ∫ t in (0:ℝ)..T, f n t := by
  have hfi (n) : IntegrableOn (f n) (Set.Ioc 0 T) := (hf n).intervalIntegrable.1
  have hL1 : Summable (fun n => ∫ t in Set.Ioc 0 T, ‖f n t‖) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _))
      (f := fun n => T*b n) _ (hb.mul_left T)
    intro n
    have hi : (∫ t in (0:ℝ)..T, ‖f n t‖) ≤ T*b n := by
      calc
        _ ≤ ∫ t in (0:ℝ)..T, b n := intervalIntegral.integral_mono_on hT
          (hf n).norm.intervalIntegrable intervalIntegrable_const (hbound n)
        _ = _ := by simp
    rwa [intervalIntegral.integral_of_le hT] at hi
  simp only [intervalIntegral.integral_of_le hT]
  exact (integral_tsum_of_summable_integral_norm hfi hL1).symm

theorem pairRHS_primeTerm_phase (X t : ℝ) (n : ℕ) :
    pairPrimeTerm n (X,t) = (pairMeanPrimeCoefficient X n:ℂ)*
      Complex.exp (-Complex.I*(Real.log (n+1:ℝ):ℂ)*t) := by
  rw [pairMeanPrimeTerm_frequency]
  unfold pairMeanCharacter pairMeanPrimeFrequency
  congr 2
  push_cast
  field_simp

theorem pairRHS_primeArch_term (X T : ℝ) (n : ℕ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    ‖∫ t in (0:ℝ)..T, pairPrimeTerm n (X,t)*star (pairRHSArch X t)‖ ≤
      (2*Real.log (T+2)/X)*(pairMeanPrimeCoefficient X n/Real.log (n+1:ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp [pairPrimeTerm_one,pairMeanPrimeCoefficient_one]
  have hX0 : 0 < X := by linarith
  have hc := pairMeanPrimeCoefficient_nonneg X hX n
  have hlog : 0 < Real.log (n+1:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))
  have he : (fun t : ℝ => pairPrimeTerm n (X,t)*star (pairRHSArch X t)) =
      fun t : ℝ => ((pairMeanPrimeCoefficient X n/X:ℝ):ℂ)*
        ((Real.log (t+2):ℂ)*Complex.exp (-Complex.I*(Real.log (n+1:ℝ):ℂ)*t)) := by
    funext t
    rw [pairRHS_primeTerm_phase]
    simp only [pairRHSArch,Complex.star_def,Complex.conj_ofReal]
    push_cast
    ring
  rw [he,intervalIntegral.integral_const_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hc hX0.le)]
  have hb := mul_le_mul_of_nonneg_left (pairRHS_log_oscillation (Real.log (n+1:ℝ)) T hlog hT)
    (div_nonneg hc hX0.le)
  convert hb using 1 <;> ring

theorem pairRHS_primeArch_interchange (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, pairPrimeSeries (X,t)*star (pairRHSArch X t)) =
      ∑' n : ℕ, ∫ t in (0:ℝ)..T, pairPrimeTerm n (X,t)*star (pairRHSArch X t) := by
  let b : ℕ → ℝ := fun n => (Real.log (T+2)/X)*pairMeanPrimeCoefficient X n
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  have hc := pairMeanPrimeCoefficient_summable X hX
  have hc' : Summable (pairMeanPrimeCoefficient X) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX _)] using hc
  have harch : ContinuousOn (pairRHSArch X) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]; exact pairRHSArch_continuous X T hT
  have hbound (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ‖pairPrimeTerm n (X,t)*star (pairRHSArch X t)‖ ≤ b n := by
    rw [norm_mul,norm_star,pairMeanPrimeTerm_frequency,norm_mul,pairMeanCharacter_norm,mul_one]
    simp only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (pairMeanPrimeCoefficient_nonneg X hX n),pairRHSArch]
    rw [abs_of_nonneg (div_nonneg (Real.log_nonneg (by linarith [ht.1])) hX0.le)]
    change _ ≤ (Real.log (T+2)/X)*pairMeanPrimeCoefficient X n
    rw [mul_comm (Real.log (T+2)/X)]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.log_le_log (by linarith [ht.1])
        (by linarith [ht.2])) hX0.le) (pairMeanPrimeCoefficient_nonneg X hX n)
  have hi := pairRHS_integral_tsum b T hT (hc'.mul_left _) (fun n =>
    mul_nonneg (div_nonneg hL hX0.le) (pairMeanPrimeCoefficient_nonneg X hX n))
    (fun n => (pairPrimeTerm_continuous n |>.comp_continuous
      (continuous_const.prodMk continuous_id) (fun t => hX)).continuousOn.mul harch.star) hbound
  simp only [Function.comp_def,Pi.mul_apply,id_eq] at hi
  convert hi using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact tsum_mul_right.symm

theorem pairRHSPrimeArchError_bound (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSPrimeArchError X T| ≤ 20*Real.log (T+2)/Real.sqrt X := by
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  have hsum := (pairRHS_coefficient_div_log_summable X hX).mul_left (2*Real.log (T+2)/X)
  have hb := tsum_of_norm_bounded hsum.hasSum (fun n => pairRHS_primeArch_term X T n hX hT)
  rw [← pairRHS_primeArch_interchange X T hX hT,tsum_mul_left] at hb
  have hc := mul_le_mul_of_nonneg_left (pairRHS_coefficient_div_log_sum X hX)
    (show 0 ≤ 2*Real.log (T+2)/X by positivity)
  unfold pairRHSPrimeArchError
  rw [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ 2*‖∫ t in (0:ℝ)..T, pairPrimeSeries (X,t)*star (pairRHSArch X t)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2*((2*Real.log (T+2)/X)*(5*Real.sqrt X)) := by gcongr; exact hb.trans hc
    _ = _ := by
      have hs := Real.sq_sqrt hX0.le
      field_simp
      nlinarith

end
end HigherCorrelations
