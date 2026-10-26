import HigherCorrelations.TripleBudgetRemainders
import HigherCorrelations.TripleBudgetUniform
import HigherCorrelations.TripleBudgetSlots

/-! UNCONDITIONAL coarse mixed and cubic bounds, independent of frequency decay.
These retain actual weighted L2 norms, with the checked two-branch envelope. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleBudget_PAPoff_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PAPoff‖ ≤ tripleBudgetAlpha T Y*
      (tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T (X*Y)+tripleBudgetDiagonal X (X*Y)) := by
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hl : 0≤Real.log (2*T+2) := Real.log_nonneg (by linarith)
  have hJ : 0≤tripleBudgetMoment ω T 1 :=
    (Real.log_nonneg (by linarith : 1≤T)).trans (by simpa using (tripleBudgetMoment_bounds ω hω T hT 1).1)
  have hJupper : tripleBudgetMoment ω T 1≤Real.log (2*T+2) := by simpa using (tripleBudgetMoment_bounds ω hω T hT 1).2
  have hD := tripleBudgetDiagonal_nonneg X (X*Y) hX hz
  have hb := tripleBudget_integral_second_sup ω hω T (by linarith)
    (fun t => pairPrimeSeries (X,t)) (tripleArch Y) (fun t => pairPrimeSeries (X*Y,t))
    (pairRHS_prime_continuous X hX) (pairRHS_prime_continuous (X*Y) hz)
    (tripleBudgetAlpha T Y) (div_nonneg hl (by linarith))
    (fun t ht => tripleBudget_arch_bound T Y t hT hY ht)
  have hd : ‖((tripleBudgetMoment ω T 1*tripleBudgetDiagonal X (X*Y)/Y:ℝ):ℂ)‖≤
      tripleBudgetAlpha T Y*tripleBudgetDiagonal X (X*Y) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    convert div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hJupper hD) (by linarith : 0≤Y) using 1 <;>
      simp only [tripleBudgetAlpha] <;> ring
  unfold tripleBudgetError
  apply (norm_sub_le _ _).trans
  change ‖tripleSmoothedIntegral ω T (fun t => pairPrimeSeries (X,t)) (tripleArch Y) (fun t => pairPrimeSeries (X*Y,t))‖ + _ ≤ _
  convert add_le_add hb hd using 1 <;> (try simp only [tripleBudgetPrimeL2,tripleBudgetL2]) <;> ring

theorem tripleBudget_APPoff_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleBudgetError ω T X Y .APPoff = tripleBudgetError ω T Y X .PAPoff := by
  have he : tripleWordIntegral ω T X Y ![.A,.P,.P] = tripleWordIntegral ω T Y X ![.P,.A,.P] := by
    apply integral_congr_ae
    filter_upwards [] with t
    change ((ω (t/T)/T:ℝ):ℂ)*tripleArch X t*pairPrimeSeries (Y,t)*star (pairPrimeSeries (X*Y,t)) =
      ((ω (t/T)/T:ℝ):ℂ)*pairPrimeSeries (Y,t)*tripleArch X t*star (pairPrimeSeries (Y*X,t))
    rw [mul_comm Y X]
    ring
  simp only [tripleBudgetError,he,mul_comm Y X]

theorem tripleBudget_APPoff_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .APPoff‖ ≤ tripleBudgetAlpha T X*
      (tripleBudgetPrimeL2 ω T Y*tripleBudgetPrimeL2 ω T (X*Y)+tripleBudgetDiagonal Y (X*Y)) := by
  rw [tripleBudget_APPoff_swap]
  simpa only [mul_comm Y X] using tripleBudget_PAPoff_coarse ω hω T Y X hT hY hX

theorem tripleBudget_PPP_coarse (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleWordIntegral ω T X Y ![.P,.P,.P]‖ ≤
      min (min (triplePrimeMass X*tripleBudgetPrimeL2 ω T Y*tripleBudgetPrimeL2 ω T (X*Y))
        (triplePrimeMass Y*tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T (X*Y)))
        (triplePrimeMass (X*Y)*tripleBudgetPrimeL2 ω T X*tripleBudgetPrimeL2 ω T Y) := by
  have ht : 0<T := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hm (x : ℝ) (hx : 1≤x) : 0≤triplePrimeMass x := tsum_nonneg (pairMeanPrimeCoefficient_nonneg x hx)
  change ‖tripleSmoothedIntegral ω T (fun t => pairPrimeSeries (X,t))
    (fun t => pairPrimeSeries (Y,t)) (fun t => pairPrimeSeries (X*Y,t))‖ ≤ _
  apply le_min
  · apply le_min
    · convert tripleBudget_integral_first_sup ω hω T ht _ _ _
        (pairRHS_prime_continuous Y hY) (pairRHS_prime_continuous (X*Y) hz) _ (hm X hX)
        (fun t _ => tripleBudgetPrime_sup_mass X t hX) using 1 <;> (try simp only [tripleBudgetPrimeL2,tripleBudgetL2]) <;> ring
    · convert tripleBudget_integral_second_sup ω hω T ht _ _ _
        (pairRHS_prime_continuous X hX) (pairRHS_prime_continuous (X*Y) hz) _ (hm Y hY)
        (fun t _ => tripleBudgetPrime_sup_mass Y t hY) using 1 <;> (try simp only [tripleBudgetPrimeL2,tripleBudgetL2]) <;> ring
  · convert tripleBudget_integral_norm_bound ω hω T ht _ _ _
      (pairRHS_prime_continuous X hX) (pairRHS_prime_continuous Y hY) _ (hm (X*Y) hz)
      (fun t _ => tripleBudgetPrime_sup_mass (X*Y) t hz) using 1 <;> (try simp only [tripleBudgetPrimeL2,tripleBudgetL2]) <;> ring

end
end HigherCorrelations
