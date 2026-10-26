import HigherCorrelations.TripleSameSignFourier
import HigherCorrelations.TripleBudgetMixedIdentity

/-! UNCONDITIONAL bounds for the four non-resonant words with archimedean slots.
The explicit constant five for one-prime words is stronger than the draft constant. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleBudget_PPA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0<T) :
    tripleBudgetError ω T X Y .PPA = (1/((X*Y:ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(pairPrimeSeries (X,t)*pairPrimeSeries (Y,t)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 1 t]
  change ((ω (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X,t)*pairPrimeSeries (Y,t)*star (tripleArch (X*Y) t) = _
  simp only [tripleArch,Complex.star_def,Complex.conj_ofReal,pow_one]
  push_cast
  ring

theorem tripleBudget_PAA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0<T) :
    tripleBudgetError ω T X Y .PAA = -(1/((Y*(X*Y):ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X,t) := by
  change -(∫ t, tripleWordIntegrand ω T X Y ![.P,.A,.A] t) = _
  rw [← integral_neg,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 2 t]
  change -(((ω (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X,t)*tripleArch Y t*star (tripleArch (X*Y) t)) = _
  simp only [tripleArch,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

theorem tripleBudget_APA_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0<T) :
    tripleBudgetError ω T X Y .APA = -(1/((X*(X*Y):ℝ):ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (Y,t) := by
  change -(∫ t, tripleWordIntegrand ω T X Y ![.A,.P,.A] t) = _
  rw [← integral_neg,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 2 t]
  change -(((ω (t/T)/T:ℝ):ℂ)*tripleArch X t*pairPrimeSeries (Y,t)*star (tripleArch (X*Y) t)) = _
  simp only [tripleArch,Complex.star_def,Complex.conj_ofReal]
  push_cast
  ring

theorem tripleBudget_AAP_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0<T) :
    tripleBudgetError ω T X Y .AAP = -(1/((X*Y:ℝ):ℂ))*star
      (∫ t, ((tripleBudgetLogWeight ω T 2 (t/T)/T:ℝ):ℂ)*pairPrimeSeries (X*Y,t)) := by
  change -(∫ t, tripleWordIntegrand ω T X Y ![.A,.A,.P] t) = _
  simp only [Complex.star_def]
  rw [← integral_conj,← integral_neg,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 2 t]
  change -(((ω (t/T)/T:ℝ):ℂ)*tripleArch X t*tripleArch Y t*star (pairPrimeSeries (X*Y,t))) = _
  simp only [tripleArch,Complex.star_def,map_mul,Complex.conj_ofReal]
  push_cast
  ring

theorem tripleBudget_PPA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PPA‖ ≤
      triplePrimeMass X*triplePrimeMass Y*tripleBudgetOmega ω T 1/((X*Y)*T*Real.log 4) := by
  rw [tripleBudget_PPA_identity ω hω T X Y (by linarith),norm_mul]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤X*Y)]
  convert mul_le_mul_of_nonneg_left (tripleBudget_same_sign_bound ω hω T X Y hT hX hY 1)
    (by positivity : 0≤1/(X*Y)) using 1 <;> ring

theorem tripleBudget_PAA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PAA‖ ≤ 5*Real.sqrt X*tripleBudgetOmega ω T 2/(T*Y*(X*Y)) := by
  rw [tripleBudget_PAA_identity ω hω T X Y (by linarith),norm_mul,norm_neg]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤Y*(X*Y))]
  convert mul_le_mul_of_nonneg_left (tripleBudget_single_prime_bound ω hω T X hT hX 2)
    (by positivity : 0≤1/(Y*(X*Y))) using 1 <;> ring

theorem tripleBudget_APA_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .APA‖ ≤ 5*Real.sqrt Y*tripleBudgetOmega ω T 2/(T*X*(X*Y)) := by
  rw [tripleBudget_APA_identity ω hω T X Y (by linarith),norm_mul,norm_neg]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤X*(X*Y))]
  convert mul_le_mul_of_nonneg_left (tripleBudget_single_prime_bound ω hω T Y hT hY 2)
    (by positivity : 0≤1/(X*(X*Y))) using 1 <;> ring

theorem tripleBudget_AAP_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .AAP‖ ≤ 5*Real.sqrt (X*Y)*tripleBudgetOmega ω T 2/(T*X*Y) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  rw [tripleBudget_AAP_identity ω hω T X Y (by linarith),norm_mul,norm_neg,norm_star]
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤X*Y)]
  convert mul_le_mul_of_nonneg_left (tripleBudget_single_prime_bound ω hω T (X*Y) hT hz 2)
    (by positivity : 0≤1/(X*Y)) using 1 <;> ring

end
end HigherCorrelations
