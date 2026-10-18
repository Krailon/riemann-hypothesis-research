import HigherCorrelations.PairRHSScales
import Mathlib.Algebra.Order.Chebyshev

/-! UNCONDITIONAL estimates for the signed cross terms and the full remainder square. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem pairRHSPrimeError_cauchy (j : PairRemainderKind) (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSPrimeError j X T| ≤
      2*pairPrimeMeanL2Norm X T*pairRHSL2 (pairRHSRemainder j X) T := by
  unfold pairRHSPrimeError
  rw [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := mul_le_mul_of_nonneg_left (pairRHSL2_cauchy (fun t => pairPrimeSeries (X,t))
    (pairRHSRemainder j X) T hT (pairRHS_prime_continuous X hX).continuousOn
    (pairRHS_remainder_continuous j X hX).continuousOn) (by norm_num : (0:ℝ)≤2)
  simpa only [pairRHSL2,pairPrimeMeanL2Norm,pairPrimeMeanSquare,mul_assoc] using h

theorem pairRHSArchError_cauchy (j : PairRemainderKind) (X T : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) :
    |pairRHSArchError j X T| ≤
      2*pairRHSL2 (pairRHSArch X) T*pairRHSL2 (pairRHSRemainder j X) T := by
  unfold pairRHSArchError
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := mul_le_mul_of_nonneg_left (pairRHSL2_cauchy (pairRHSArch X)
    (pairRHSRemainder j X) T hT (pairRHSArch_continuous X T hT)
    (pairRHS_remainder_continuous j X hX).continuousOn) (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h

theorem pairRHSRemainderSquare_bound (K X T : ℝ) (hK : 0 ≤ K) (hX : 1 ≤ X) (hT : 0 ≤ T)
    (hb : ∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) :
    0 ≤ pairRHSRemainderSquare X T ∧ pairRHSRemainderSquare X T ≤ 16*K^2*T := by
  have hj (j : PairRemainderKind) : Continuous (fun t => ‖pairRHSRemainder j X t‖^2) :=
    (pairRHS_remainder_continuous j X hX).norm.pow 2
  have hh : Continuous (fun t => ‖pairRHSRemainderSum X t‖^2) :=
    (continuous_finsetSum _ (fun j _ => pairRHS_remainder_continuous j X hX)).norm.pow 2
  have hcard : (Finset.univ : Finset PairRemainderKind).card = 4 := by
    decide
  have hi (j : PairRemainderKind) : (∫ t in (0:ℝ)..T, ‖pairRHSRemainder j X t‖^2) ≤ K^2*T := by
    have hnon : 0 ≤ (∫ t in (0:ℝ)..T, ‖pairRHSRemainder j X t‖^2) :=
      intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg _)
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb j) 2
    simpa only [pairRHSL2,Real.sq_sqrt hnon,mul_pow,Real.sq_sqrt hT] using h
  refine ⟨intervalIntegral.integral_nonneg_of_forall hT (fun t => sq_nonneg _),?_⟩
  calc
    _ ≤ ∫ t in (0:ℝ)..T, 4*(∑ j, ‖pairRHSRemainder j X t‖^2) := by
      apply intervalIntegral.integral_mono_on hT (hh.intervalIntegrable 0 T)
        (((continuous_finsetSum _ (fun j _ => hj j)).const_mul 4).intervalIntegrable 0 T)
      intro t ht
      have hnorm := norm_sum_le (Finset.univ : Finset PairRemainderKind)
        (fun j => pairRHSRemainder j X t)
      have hs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset PairRemainderKind))
        (f := fun j => ‖pairRHSRemainder j X t‖)
      rw [hcard] at hs
      exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by simpa using hs)
    _ = 4*(∑ j, ∫ t in (0:ℝ)..T, ‖pairRHSRemainder j X t‖^2) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum
        (fun j _ => (hj j).intervalIntegrable 0 T)]
    _ ≤ 4*(∑ _j : PairRemainderKind, K^2*T) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hi j)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,← Finset.card_univ,hcard,nsmul_eq_mul]; ring

theorem pairRHSPrimeError_scale (C K X T : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (hp : pairPrimeMeanL2Norm X T ≤ C*Real.sqrt (T*Real.log (2*X)))
    (he : ∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) (j : PairRemainderKind) :
    |pairRHSPrimeError j X T| ≤ 4*C*K*(T*Real.sqrt (Real.log T)) := by
  have hs := (pairRHS_height_scales X T hX hT hXT).2.2.2.1
  have hT0 : 0 ≤ T := by linarith
  calc
    _ ≤ 2*pairPrimeMeanL2Norm X T*pairRHSL2 (pairRHSRemainder j X) T :=
      pairRHSPrimeError_cauchy j X T hX hT0
    _ ≤ 2*(C*(2*Real.sqrt T*Real.sqrt (Real.log T)))*(K*Real.sqrt T) := by
      gcongr
      · exact Real.sqrt_nonneg _
      · exact hp.trans (mul_le_mul_of_nonneg_left hs hC)
      · exact he j
    _ = _ := by ring_nf; rw [Real.sq_sqrt hT0]; ring

theorem pairRHSArchError_small (K X T : ℝ) (j : PairRemainderKind) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T)
    (he : pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T/X) :
    |pairRHSArchError j X T| ≤ 4*K*(T*Real.log T/X^2) := by
  have hT0 : 0 ≤ T := by linarith
  have hq : 0 ≤ Real.log T := by linarith [(pairRHS_log_comparison T hT).1]
  have hX0 : 0 < X := by linarith
  calc
    _ ≤ 2*pairRHSL2 (pairRHSArch X) T*pairRHSL2 (pairRHSRemainder j X) T :=
      pairRHSArchError_cauchy j X T hX hT0
    _ ≤ 2*(2*Real.sqrt T*Real.log T/X)*(K*Real.sqrt T/X) := by
      gcongr
      · exact Real.sqrt_nonneg _
      · exact pairRHS_arch_L2 X T hX hT
    _ = _ := by field_simp; ring_nf; rw [Real.sq_sqrt hT0]; ring

theorem pairRHSArchError_large (K X T : ℝ) (j : PairRemainderKind) (hK : 0 ≤ K)
    (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T)
    (he : pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt X) :
    |pairRHSArchError j X T| ≤ 4*K*(T*Real.sqrt (Real.log T)) := by
  have hT0 : 0 ≤ T := by linarith
  have hq : 0 ≤ Real.log T := by linarith [(pairRHS_log_comparison T hT).1]
  have hX0 : 0 < X := by linarith
  have hsX : Real.sqrt X ≤ X := (Real.sqrt_le_left hX0.le).mpr (by nlinarith)
  have hsq := (pairRHS_height_scales X T hX hT hXT).2.2.2.2.2
  calc
    _ ≤ 2*pairRHSL2 (pairRHSArch X) T*pairRHSL2 (pairRHSRemainder j X) T :=
      pairRHSArchError_cauchy j X T hX hT0
    _ ≤ 2*(2*Real.sqrt T*Real.log T/X)*(K*X) := by
      gcongr
      · exact Real.sqrt_nonneg _
      · exact pairRHS_arch_L2 X T hX hT
      · exact he.trans (mul_le_mul_of_nonneg_left hsX hK)
    _ = 4*K*(Real.sqrt T*Real.log T) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)

end
end HigherCorrelations
