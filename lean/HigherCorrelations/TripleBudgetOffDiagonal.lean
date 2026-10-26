import HigherCorrelations.TripleBudgetMixedIdentity
import HigherCorrelations.TripleConvolutionDiagonal
import HigherCorrelations.TripleArithmeticGapBounds

/-! UNCONDITIONAL bounds on the actual named mixed and cubic off-diagonal errors.
No zero coordinate is specialized, and no restriction XY <= 2T is used. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudget_PPPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleBudgetError ω T X Y .PPPoff =
      -(∑' p, tripleLogFourierOffTerm ω T (tripleLogConvolution X Y)
        (tripleLogCoefficient (X*Y)) p) := by
  have ht : 0<T := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have he := tripleLogFourier_off_identity ω (tripleBudgetWeight_integrable ω hω) T ht _ _
    (tripleLogConvolution_mass_summable X Y hX hY) (tripleLogCoefficient_mass_summable (X*Y) hz)
  simp_rw [tripleLogConvolution_series X Y _ hX hY,tripleLogCoefficient_series (X*Y) _ hz] at he
  rw [tripleLogConvolution_diagonal X Y hX hY,integral_complex_ofReal,hω.mass,
    Complex.ofReal_one,mul_one] at he
  rw [← he]
  have hi : tripleWordIntegral ω T X Y ![.P,.P,.P] =
      ∫ t, ((ω (t/T)/T:ℝ):ℂ)*((pairPrimeSeries (X,t)*pairPrimeSeries (Y,t))*star (pairPrimeSeries (X*Y,t))) := by
    apply integral_congr_ae
    filter_upwards [] with t
    change ((ω (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X,t)*pairPrimeSeries (Y,t)*
      star (pairPrimeSeries (X*Y,t)) = _
    ring
  rw [tripleBudgetError,hi]
  ring

theorem tripleBudget_PAPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤
      (tripleBudgetOmega ω T 1/(T*Y))*tripleLogGapBound (tripleLogCoefficient X) (tripleLogCoefficient (X*Y)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hb := tripleLogFourierOff_bound (tripleBudgetLogWeight ω T 1)
    ((tripleBudgetLogWeight_smooth ω hω T hT 1).of_le (by simp))
    (tripleBudgetLogWeight_compact ω hω T 1) T (by linarith) _ _
    (tripleLogCoefficient_mass_summable X hX) (tripleLogCoefficient_mass_summable (X*Y) hz)
    (tripleLogCoefficient_energy_summable X hX) (tripleLogCoefficient_energy_summable (X*Y) hz)
  rw [tripleBudget_PAPoff_identity ω hω T X Y hT hX hY,norm_mul]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Y)]
  convert mul_le_mul_of_nonneg_left hb (by positivity : 0≤1/Y) using 1 <;>
    simp only [tripleBudgetOmega] <;> ring

theorem tripleBudget_APPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤
      (tripleBudgetOmega ω T 1/(T*X))*tripleLogGapBound (tripleLogCoefficient Y) (tripleLogCoefficient (X*Y)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hb := tripleLogFourierOff_bound (tripleBudgetLogWeight ω T 1)
    ((tripleBudgetLogWeight_smooth ω hω T hT 1).of_le (by simp))
    (tripleBudgetLogWeight_compact ω hω T 1) T (by linarith) _ _
    (tripleLogCoefficient_mass_summable Y hY) (tripleLogCoefficient_mass_summable (X*Y) hz)
    (tripleLogCoefficient_energy_summable Y hY) (tripleLogCoefficient_energy_summable (X*Y) hz)
  rw [tripleBudget_APPoff_identity ω hω T X Y hT hX hY,norm_mul]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤X)]
  convert mul_le_mul_of_nonneg_left hb (by positivity : 0≤1/X) using 1 <;>
    simp only [tripleBudgetOmega] <;> ring

theorem tripleBudget_PPPoff_gap (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PPPoff‖ ≤
      (fourierDerivativeL1 ω 1/T)*tripleLogGapBound (tripleLogConvolution X Y) (tripleLogCoefficient (X*Y)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  rw [tripleBudget_PPPoff_identity ω hω T X Y hT hX hY,norm_neg]
  exact tripleLogFourierOff_bound ω (hω.smooth.of_le (by simp))
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (tripleBudgetWeight_support ω hω))
    T (by linarith) _ _ (tripleLogConvolution_mass_summable X Y hX hY)
    (tripleLogCoefficient_mass_summable (X*Y) hz) (tripleLogConvolution_energy_summable X Y hX hY)
    (tripleLogCoefficient_energy_summable (X*Y) hz)

end
end HigherCorrelations
