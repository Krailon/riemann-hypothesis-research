import HigherCorrelations.TripleResonanceDecayDefinitions
import HigherCorrelations.TripleConvolutionDiagonal
import HigherCorrelations.PairDiagonalAlgebra

/-! UNCONDITIONAL reduction of the actual ordered resonance to a nonnegative
proper-power majorant. No new arithmetic estimate is assumed. -/
namespace HigherCorrelations
noncomputable section
open scoped ArithmeticFunction.vonMangoldt

theorem tripleArithmeticConvolution_prime (X Y : ℝ) (p : ℕ) (hp : p.Prime) :
    tripleArithmeticConvolution X Y p = 0 := by
  simp [tripleArithmeticConvolution,hp.divisors,Nat.div_self hp.pos,tripleArithmeticCoefficient_one]

theorem tripleResonance_support (X Y : ℝ) (n : ℕ)
    (hn : ¬(IsPrimePow n ∧ ¬n.Prime)) :
    tripleArithmeticConvolution X Y n*tripleArithmeticCoefficient (X*Y) n = 0 := by
  by_cases hp : n.Prime
  · rw [tripleArithmeticConvolution_prime X Y n hp,zero_mul]
  · have hpp : ¬IsPrimePow n := fun h => hn ⟨h,hp⟩
    simp [tripleArithmeticCoefficient,ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]

theorem tripleResonanceMajorant_nonneg (Z : ℝ) (n : ℕ) :
    0 ≤ tripleResonanceMajorant Z n := by
  unfold tripleResonanceMajorant
  split_ifs with hn
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.1.ne_zero
    have hl := Real.log_nonneg (show (1:ℝ) ≤ n by exact_mod_cast hn1)
    positivity
  · rfl

theorem tripleResonance_pointwise (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (n : ℕ) :
    tripleArithmeticConvolution X Y n*tripleArithmeticCoefficient (X*Y) n ≤
      tripleResonanceMajorant (X*Y) n := by
  by_cases hn : IsPrimePow n ∧ ¬n.Prime
  · have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn.1.ne_zero
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn.1.ne_zero
    have hZ : 1 ≤ X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
    have hv := tripleMultiplicativeWeight_nonneg (X*Y) (by positivity) n
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hc := tripleArithmeticConvolution_bound X Y hX hY n hn1
    have hc2 : tripleArithmeticCoefficient (X*Y) n ≤
        Real.log n/Real.sqrt n*tripleMultiplicativeWeight (X*Y) n := by
      unfold tripleArithmeticCoefficient
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        ArithmeticFunction.vonMangoldt_le_log (Real.sqrt_nonneg _)) hv
    have hb := mul_le_mul hc hc2 (tripleArithmeticCoefficient_nonneg (X*Y) hZ n) (by positivity)
    unfold tripleResonanceMajorant
    rw [if_pos hn]
    convert hb using 1
    have hs := Real.sq_sqrt hn0.le
    have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    field_simp
    rw [hs]
  · rw [tripleResonance_support X Y n hn,tripleResonanceMajorant,if_neg hn]

theorem tripleResonance_weight_identity (Z : ℝ) (hZ : 1 ≤ Z) (n : ℕ) (hn : 0 < n) :
    tripleMultiplicativeWeight Z n^2/(n:ℝ) = pairDiagonalWeight Z n := by
  have hZ0 : 0 < Z := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  unfold tripleMultiplicativeWeight pairDiagonalWeight
  split_ifs with h
  · have hm : (n:ℝ)/Z ≤ Z/n := by
      apply (div_le_div_iff₀ hZ0 hn0).mpr
      nlinarith
    rw [min_eq_left hm]
    field_simp
  · have hm : Z/(n:ℝ) ≤ n/Z := by
      apply (div_le_div_iff₀ hn0 hZ0).mpr
      nlinarith [le_of_not_ge h]
    rw [min_eq_right hm]
    field_simp

end
end HigherCorrelations
