import HigherCorrelations.PairRHSRemainderNorms
import HigherCorrelations.PairPrimeMean

/-! UNCONDITIONAL scale comparisons on the closed range 3≤T and 1≤X≤T. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHS_height_scales (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hXT : X ≤ T) :
    1 ≤ Real.sqrt T ∧ 1 ≤ Real.sqrt (Real.log T) ∧
    Real.log (2*X) ≤ 2*Real.log T ∧
    Real.sqrt (T*Real.log (2*X)) ≤ 2*Real.sqrt T*Real.sqrt (Real.log T) ∧
    Real.sqrt (T*X*Real.log (2*X)) ≤ 2*T*Real.sqrt (Real.log T) ∧
    Real.sqrt T*Real.log T ≤ T*Real.sqrt (Real.log T) := by
  obtain ⟨hq,hqt,_,_,_⟩ := pairRHS_log_comparison T hT
  have hT0 : 0 ≤ T := by linarith
  have hq0 : 0 ≤ Real.log T := by linarith
  have hsT : 1 ≤ Real.sqrt T := (Real.le_sqrt (by norm_num) hT0).mpr (by nlinarith)
  have hsq : 1 ≤ Real.sqrt (Real.log T) := (Real.le_sqrt (by norm_num) hq0).mpr (by nlinarith)
  have hell : Real.log (2*X) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (2*T) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2+Real.log T := Real.log_mul (by norm_num) (by linarith)
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have hell0 : 0 ≤ Real.log (2*X) := Real.log_nonneg (by linarith)
  have hsqT := Real.sq_sqrt hT0
  have hsqq := Real.sq_sqrt hq0
  refine ⟨hsT,hsq,hell,?_,?_,?_⟩
  · apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,mul_pow,hsqT,hsqq]
    nlinarith [mul_le_mul_of_nonneg_left hell hT0]
  · apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow,hsqq]
    have h1 : T*X*Real.log (2*X) ≤ T*T*(2*Real.log T) := by
      gcongr
    nlinarith
  · have hst : Real.sqrt (Real.log T) ≤ Real.sqrt T := Real.sqrt_le_sqrt hqt
    have h := mul_le_mul_of_nonneg_left hst
      (show 0 ≤ Real.sqrt T*Real.sqrt (Real.log T) by positivity)
    nlinarith

theorem pairRHS_remainder_uniform : ∃ K : ℝ, 0 < K ∧ ∀ X T : ℝ,
    1 ≤ X → 3 ≤ T → X ≤ T →
    (∀ j, pairRHSL2 (pairRHSRemainder j X) T ≤ K*Real.sqrt T) ∧
    pairRHSL2 (pairRHSRemainder .arch X) T ≤ K*Real.sqrt T/X ∧
    pairRHSL2 (pairRHSRemainder .ds X) T ≤ K*Real.sqrt T/X ∧
    pairRHSL2 (pairRHSRemainder .pole X) T ≤ K*Real.sqrt X ∧
    pairRHSL2 (pairRHSRemainder .trivial X) T ≤ K*Real.sqrt X := by
  let K := |pairArchConstant|+pairDSConstant+32
  have hD := pairDSConstant_nonneg
  have hK : 0 < K := by dsimp [K]; positivity
  have hKa : |pairArchConstant| ≤ K := by dsimp [K]; linarith
  have hKd : pairDSConstant ≤ K := by dsimp [K]; linarith [abs_nonneg pairArchConstant]
  have hK24 : 24 ≤ K := by dsimp [K]; linarith [abs_nonneg pairArchConstant]
  refine ⟨K,hK,?_⟩
  intro X T hX hT hXT
  have hX0 : 0 < X := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hsX : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0.le).mpr (by nlinarith)
  have hsXT := Real.sqrt_le_sqrt hXT
  have hsT := (pairRHS_height_scales X T hX hT hXT).1
  have hxpow : X^(-5/2:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num)
  have ha := (pairRHS_archError_L2 X T hX hT0).trans (by
    gcongr : |pairArchConstant| *Real.sqrt T/X ≤ K*Real.sqrt T/X)
  have hd := (pairRHS_dsError_L2 X T hX hT0).trans (by
    gcongr : pairDSConstant*Real.sqrt T/X ≤ K*Real.sqrt T/X)
  have hp := (pairRHS_pole_L2 X T hX hT0).trans (by
    gcongr; linarith : 8*Real.sqrt X ≤ K*Real.sqrt X)
  have ht : pairRHSL2 (pairRHSRemainder .trivial X) T ≤ K*Real.sqrt X := by
    calc
      _ ≤ 24*X^(-5/2:ℝ) := pairRHS_trivial_L2 X T hX hT0
      _ ≤ 24 := by nlinarith
      _ ≤ K*Real.sqrt X := by nlinarith
  refine ⟨?_,ha,hd,hp,ht⟩
  intro j
  have hdiv : K*Real.sqrt T/X ≤ K*Real.sqrt T :=
    div_le_self (by positivity) hX
  cases j
  · exact ha.trans hdiv
  · exact hd.trans hdiv
  · exact hp.trans (by gcongr)
  · exact ht.trans (by gcongr)

end
end HigherCorrelations
