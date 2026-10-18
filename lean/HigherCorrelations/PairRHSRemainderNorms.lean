import HigherCorrelations.PairRHSContinuity
import HigherCorrelations.PairRHSL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! UNCONDITIONAL. Each actual remainder is estimated separately in L2. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHSL2_constant_bound (f : ℝ → ℂ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Set.Icc 0 T)) (hb : ∀ t ∈ Set.Icc 0 T, ‖f t‖ ≤ B) :
    pairRHSL2 f T ≤ B*Real.sqrt T := by
  apply pairRHSL2_square_bound _ _ _ (by positivity)
  have hi : IntervalIntegrable (fun t => ‖f t‖^2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hf.norm.pow 2
  calc
    _ ≤ ∫ t in (0:ℝ)..T, B^2 := intervalIntegral.integral_mono_on hT hi
      (intervalIntegrable_const) (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hb t ht) 2)
    _ = _ := by simp [mul_pow,Real.sq_sqrt hT]; ring

theorem pairRHSL2_decay_bound (f : ℝ → ℂ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖f t‖^2 ≤ B^2/(1+t^2)) :
    pairRHSL2 f T ≤ 2*B := by
  apply pairRHSL2_square_bound _ _ _ (by positivity)
  have hi : IntervalIntegrable (fun t => ‖f t‖^2) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT]
    exact hf.norm.pow 2
  have hj : IntervalIntegrable (fun t : ℝ => (1+t^2)⁻¹) volume 0 T :=
    integrable_inv_one_add_sq.intervalIntegrable
  have hm : (∫ t in (0:ℝ)..T, (1+t^2)⁻¹) ≤ 4 := by
    rw [intervalIntegral.integral_of_le hT]
    have h := setIntegral_le_integral (s := Set.Ioc 0 T) integrable_inv_one_add_sq
      (Filter.Eventually.of_forall (fun t : ℝ => by positivity))
    rw [integral_univ_inv_one_add_sq] at h
    exact h.trans Real.pi_lt_four.le
  calc
    _ ≤ ∫ t in (0:ℝ)..T, B^2*(1+t^2)⁻¹ := intervalIntegral.integral_mono_on hT hi
      (hj.const_mul _) (by simpa only [div_eq_mul_inv] using hb)
    _ = B^2*(∫ t in (0:ℝ)..T, (1+t^2)⁻¹) := intervalIntegral.integral_const_mul _ _
    _ ≤ B^2*4 := mul_le_mul_of_nonneg_left hm (sq_nonneg B)
    _ = _ := by ring

theorem pairRHS_arch_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    pairRHSL2 (pairRHSArch X) T ≤ 2*Real.sqrt T*Real.log T/X := by
  have hX0 : 0 < X := by linarith
  have hlog := pairRHS_log_comparison T hT
  have hq : 0 ≤ Real.log T := by linarith [hlog.1]
  have h := pairRHSL2_constant_bound (pairRHSArch X) T (2*Real.log T/X)
    (by linarith) (by positivity) (pairRHSArch_continuous X T (by linarith)) (by
      intro t ht
      simp only [pairRHSArch,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (Real.log_nonneg (by linarith [ht.1])) hX0.le)]
      exact div_le_div_of_nonneg_right
        ((Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2])).trans hlog.2.2.2.2) hX0.le)
  convert h using 1 <;> ring

theorem pairRHS_archError_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .arch X) T ≤ |pairArchConstant| *Real.sqrt T/X := by
  have hX0 : 0 < X := by linarith
  have h := pairRHSL2_constant_bound (pairRHSRemainder .arch X) T (|pairArchConstant|/X)
    hT (by positivity) (pairRHS_remainder_continuous .arch X hX).continuousOn (by
      intro t ht
      exact (pairArchError_bound X t hX).trans
        (div_le_div_of_nonneg_right (le_abs_self _) hX0.le))
  convert h using 1 <;> ring

theorem pairRHS_dsError_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .ds X) T ≤ pairDSConstant*Real.sqrt T/X := by
  have h := pairRHSL2_constant_bound (pairRHSRemainder .ds X) T (pairDSConstant/X)
    hT (div_nonneg pairDSConstant_nonneg (by linarith))
    (pairRHS_remainder_continuous .ds X hX).continuousOn (fun t _ => pairDSError_bound X t hX)
  convert h using 1 <;> ring

theorem pairRHS_pole_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .pole X) T ≤ 8*Real.sqrt X := by
  have hX0 : 0 ≤ X := by linarith
  have h := pairRHSL2_decay_bound (pairRHSRemainder .pole X) T (4*Real.sqrt X)
    hT (by positivity) (pairRHS_remainder_continuous .pole X hX).continuousOn (by
      intro t ht
      have hb := pairPoleCorrection_bound X t hX
      rw [← Real.sqrt_eq_rpow] at hb
      have hd : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
      have hn : (0:ℝ) < 1+t^2 := by positivity
      calc
        _ ≤ (4*Real.sqrt X/(1+t^2))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ ≤ (4*Real.sqrt X)^2/(1+t^2) := by
          rw [div_pow]
          apply div_le_div_of_nonneg_left (sq_nonneg _) hn
          nlinarith [sq_nonneg (t^2)] )
  convert h using 1 <;> ring

theorem pairRHS_trivial_L2 (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    pairRHSL2 (pairRHSRemainder .trivial X) T ≤ 24*X^(-5/2:ℝ) := by
  have hX0 : 0 ≤ X := by linarith
  have h := pairRHSL2_decay_bound (pairRHSRemainder .trivial X) T (12*X^(-5/2:ℝ))
    hT (by positivity) (pairRHS_remainder_continuous .trivial X hX).continuousOn (by
      intro t ht
      have hb := pairTrivialCorrection_bound X t hX
      rw [abs_of_nonneg ht.1] at hb
      calc
        _ ≤ (12*X^(-5/2:ℝ)/(t+2))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ ≤ (12*X^(-5/2:ℝ))^2/(1+t^2) := by
          rw [div_pow]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          nlinarith [ht.1])
  convert h using 1 <;> ring

end
end HigherCorrelations
