import HigherCorrelations.PairExactFormula
import HigherCorrelations.PairArchErrorBound
import HigherCorrelations.PairDSConstantTail
import HigherCorrelations.PairTrivialErrorBound

/-! PAIR-EF-001 in the project's exact conventions. UNCONDITIONAL.
All statements hold for X≥1 and every real t, with all actual zero occurrences
and their analytic multiplicities. Constants are independent of X and t. -/
namespace HigherCorrelations
noncomputable section

theorem pairUniform_shift_split (X t : ℝ) :
    -pairShiftCorrection (X,t) = (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ) +
      pairArchError (X,t)+pairDSError (X,t) := by
  have h := pairShift_logDeriv_split t
  unfold pairShiftCorrection pairArchError pairDSError
  dsimp only [Prod.fst,Prod.snd]
  linear_combination (X:ℂ)⁻¹ * h

theorem pairUniform_formula (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t) +
      (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ) + pairArchError (X,t)+pairDSError (X,t) +
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by
  rw [pairExact_formula X t hX, sub_eq_add_neg, pairUniform_shift_split]
  ring

theorem pairUniform_named_bounds (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairArchError (X,t)‖ ≤ pairArchConstant/X ∧
    ‖pairDSError (X,t)‖ ≤ pairDSConstant/X ∧
    ‖pairPoleCorrection (X,t)‖ ≤ 4*X^(1/2:ℝ)/(1+t^2) ∧
    ‖pairTrivialCorrection (X,t)‖ ≤ 12*X^(-5/2:ℝ)/(|t|+2) :=
  ⟨pairArchError_bound X t hX, pairDSError_bound X t hX,
    pairPoleCorrection_bound X t hX, pairTrivialCorrection_bound X t hX⟩

theorem pairUniform_remainder_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroSeries (X,t)+pairPrimeSeries (X,t)-
      (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ)‖ ≤
      (pairArchConstant+pairDSConstant)/X +
        4*X^(1/2:ℝ)/(1+t^2)+12*X^(-5/2:ℝ)/(|t|+2) := by
  rw [pairUniform_formula X t hX]
  have he : -pairPrimeSeries (X,t)+(X:ℂ)⁻¹*(Real.log (|t|+2):ℂ)+
      pairArchError (X,t)+pairDSError (X,t)+pairPoleCorrection (X,t)+
      pairTrivialCorrection (X,t)+pairPrimeSeries (X,t)-
      (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ) =
      pairArchError (X,t)+pairDSError (X,t)+pairPoleCorrection (X,t)+
        pairTrivialCorrection (X,t) := by ring
  rw [he, add_div]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (pairArchError_bound X t hX)
        (pairDSError_bound X t hX))) (pairPoleCorrection_bound X t hX)))
    (pairTrivialCorrection_bound X t hX))

theorem pairUniform_endpoint (t : ℝ) :
    pairZeroSeries (1,t) = -pairPrimeSeries (1,t)+(Real.log (|t|+2):ℂ)+
      pairArchError (1,t)+pairDSError (1,t)+pairPoleCorrection (1,t)+
        pairTrivialCorrection (1,t) := by
  simpa using pairUniform_formula 1 t (by norm_num)

theorem pairUniform_zero_height (X : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroSeries (X,0)+pairPrimeSeries (X,0)-(X:ℂ)⁻¹*(Real.log 2:ℂ)‖ ≤
      (pairArchConstant+pairDSConstant)/X+4*X^(1/2:ℝ)+6*X^(-5/2:ℝ) := by
  convert pairUniform_remainder_bound X 0 hX using 1 <;> norm_num <;> ring

end
end HigherCorrelations
