import HigherCorrelations.TripleBudgetOffDiagonal
import HigherCorrelations.TripleGapRates

/-! UNCONDITIONAL decaying bounds for the three named errors, valid for every
T >= 3 and X,Y >= 1, without the mean-square cutoff XY <= 2T. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudget_PAPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (tripleBudgetOmega ω T 1/T)*(X/Real.sqrt Y)*
          Real.sqrt (Real.log (2*X)^3*Real.log (2*(X*Y))^3) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have h := mul_le_mul_of_nonneg_left (tripleLogGap_mixed_rate X (X*Y) hX hz)
    (show 0≤tripleBudgetOmega ω T 1/(T*Y) from
      div_nonneg (fourierDerivativeL1_nonneg _ _) (by positivity))
  apply (tripleBudget_PAPoff_gap ω hω T X Y hT hX hY).trans
  have hs : Real.sqrt X*Real.sqrt (X*Y)/Y = X/Real.sqrt Y := by
    rw [Real.sqrt_mul (by linarith : 0≤X)]
    have hy : Real.sqrt Y≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    field_simp
    nlinarith [Real.sq_sqrt (by linarith : 0≤X),Real.sq_sqrt (by linarith : 0≤Y)]
  calc
    _ ≤ _ := h
    _ = _ := by
      calc
        _ = (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
            (tripleBudgetOmega ω T 1/T)*(Real.sqrt X*Real.sqrt (X*Y)/Y)*
              Real.sqrt (Real.log (2*X)^3*Real.log (2*(X*Y))^3) := by ring
        _ = _ := by rw [hs]

theorem tripleBudget_APPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤
      (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
        (tripleBudgetOmega ω T 1/T)*(Y/Real.sqrt X)*
          Real.sqrt (Real.log (2*Y)^3*Real.log (2*(X*Y))^3) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have h := mul_le_mul_of_nonneg_left (tripleLogGap_mixed_rate Y (X*Y) hY hz)
    (show 0≤tripleBudgetOmega ω T 1/(T*X) from
      div_nonneg (fourierDerivativeL1_nonneg _ _) (by positivity))
  apply (tripleBudget_APPoff_gap ω hω T X Y hT hX hY).trans
  have hs : Real.sqrt Y*Real.sqrt (X*Y)/X = Y/Real.sqrt X := by
    rw [mul_comm X Y,Real.sqrt_mul (by linarith : 0≤Y)]
    have hx : Real.sqrt X≠0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    field_simp
    nlinarith [Real.sq_sqrt (by linarith : 0≤X),Real.sq_sqrt (by linarith : 0≤Y)]
  calc
    _ ≤ _ := h
    _ = _ := by
      calc
        _ = (triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3)*
            (tripleBudgetOmega ω T 1/T)*(Real.sqrt Y*Real.sqrt (X*Y)/X)*
              Real.sqrt (Real.log (2*Y)^3*Real.log (2*(X*Y))^3) := by ring
        _ = _ := by rw [hs]

theorem tripleBudget_PPPoff_rate (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PPPoff‖ ≤
      (triplePrimeMassConstant^3/Real.log 2^2+4*Real.sqrt 2*Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3))*
        fourierDerivativeL1 ω 1*(X*Y)*Real.log (2*(X*Y))^4/T := by
  apply (tripleBudget_PPPoff_gap ω hω T X Y hT hX hY).trans
  convert mul_le_mul_of_nonneg_left (tripleLogGap_cubic_rate X Y hX hY)
    (div_nonneg (fourierDerivativeL1_nonneg ω 1) (by linarith : 0≤T)) using 1 <;> ring

end
end HigherCorrelations
