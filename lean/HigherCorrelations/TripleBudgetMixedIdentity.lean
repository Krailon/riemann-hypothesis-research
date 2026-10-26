import HigherCorrelations.TripleArithmeticFourier
import HigherCorrelations.TripleBudgetOscillation
import HigherCorrelations.TripleBudgetDiagonal

/-! UNCONDITIONAL mixed-prime diagonal extraction for the two ordered slots.
The logarithmic smoothing moment and the coefficient diagonal remain exact. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleLogCoefficient_diagonal (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    (∑' n : LogGapIndex, tripleLogCoefficient X n*star (tripleLogCoefficient Y n)) =
      (tripleBudgetDiagonal X Y:ℂ) := by
  have hs := tripleBudgetDiagonal_summable X Y hX hY
  simp only [tripleLogCoefficient,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
  rw [← Complex.ofReal_tsum]
  congr 1
  rw [tripleNat_tsum_ge_two (fun n => tripleArithmeticCoefficient X n*tripleArithmeticCoefficient Y n)
    (by simp [tripleArithmeticCoefficient_zero]) (by simp [tripleArithmeticCoefficient_one])]
  have hi : Summable (fun n : ℕ => tripleArithmeticCoefficient X n*tripleArithmeticCoefficient Y n) :=
    (summable_nat_add_iff 1).mp (by simpa only [tripleArithmeticCoefficient_succ] using hs)
  rw [hi.tsum_eq_zero_add]
  simp only [tripleArithmeticCoefficient_zero,zero_mul,zero_add,tripleArithmeticCoefficient_succ,tripleBudgetDiagonal]

theorem tripleBudgetLogWeight_scaled (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (r : ℕ) (t : ℝ) :
    tripleBudgetLogWeight ω T r (t/T) = ω (t/T)*Real.log (|t|+2)^r := by
  rw [tripleBudgetLogWeight_eq_abs ω hω T hT.le r]
  congr 3
  field_simp

theorem tripleBudget_arch_middle (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (y : ℝ) (f g : ℝ → ℂ) :
    tripleSmoothedIntegral ω T f (tripleArch y) g = (1/(y:ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(f t*star (g t)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 1 t]
  simp only [tripleSmoothedIntegrand,tripleArch,pow_one]
  push_cast
  ring

theorem tripleBudget_arch_first (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0<T) (x : ℝ) (f g : ℝ → ℂ) :
    tripleSmoothedIntegral ω T (tripleArch x) f g = (1/(x:ℂ))*
      ∫ t, ((tripleBudgetLogWeight ω T 1 (t/T)/T:ℝ):ℂ)*(f t*star (g t)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [tripleBudgetLogWeight_scaled ω hω T hT 1 t]
  simp only [tripleSmoothedIntegrand,tripleArch,pow_one]
  push_cast
  ring

theorem tripleBudget_PAPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleBudgetError ω T X Y .PAPoff = (1/(Y:ℂ))*
      ∑' p, tripleLogFourierOffTerm (tripleBudgetLogWeight ω T 1) T
        (tripleLogCoefficient X) (tripleLogCoefficient (X*Y)) p := by
  have ht : 0<T := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have he := tripleLogFourier_off_identity (tripleBudgetLogWeight ω T 1)
    (tripleBudgetLogWeight_integrable ω hω T hT 1) T ht _ _
    (tripleLogCoefficient_mass_summable X hX) (tripleLogCoefficient_mass_summable (X*Y) hz)
  simp_rw [tripleLogCoefficient_series X _ hX,tripleLogCoefficient_series (X*Y) _ hz] at he
  rw [tripleLogCoefficient_diagonal X (X*Y) hX hz,integral_complex_ofReal,
    tripleBudgetLogWeight_integral ω hω T ht.le 1] at he
  change tripleSmoothedIntegral ω T (fun t => pairPrimeSeries (X,t)) (tripleArch Y)
    (fun t => pairPrimeSeries (X*Y,t)) - _ = _
  rw [tripleBudget_arch_middle ω hω T ht Y,← he]
  push_cast
  ring

theorem tripleBudget_APPoff_identity (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleBudgetError ω T X Y .APPoff = (1/(X:ℂ))*
      ∑' p, tripleLogFourierOffTerm (tripleBudgetLogWeight ω T 1) T
        (tripleLogCoefficient Y) (tripleLogCoefficient (X*Y)) p := by
  have ht : 0<T := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have he := tripleLogFourier_off_identity (tripleBudgetLogWeight ω T 1)
    (tripleBudgetLogWeight_integrable ω hω T hT 1) T ht _ _
    (tripleLogCoefficient_mass_summable Y hY) (tripleLogCoefficient_mass_summable (X*Y) hz)
  simp_rw [tripleLogCoefficient_series Y _ hY,tripleLogCoefficient_series (X*Y) _ hz] at he
  rw [tripleLogCoefficient_diagonal Y (X*Y) hY hz,integral_complex_ofReal,
    tripleBudgetLogWeight_integral ω hω T ht.le 1] at he
  change tripleSmoothedIntegral ω T (tripleArch X) (fun t => pairPrimeSeries (Y,t))
    (fun t => pairPrimeSeries (X*Y,t)) - _ = _
  rw [tripleBudget_arch_first ω hω T ht X,← he]
  push_cast
  ring

end
end HigherCorrelations
