import HigherCorrelations.TripleLinearFourier

/-! UNCONDITIONAL same-sign product bound: the first possible product frequency
is integer four, and all coefficients below it vanish exactly. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem tripleArithmeticConvolution_below_four (X Y : ℝ) (r : ℕ) (hr : r<4) :
    tripleArithmeticConvolution X Y r=0 := by
  interval_cases r <;>
    norm_num [tripleArithmeticConvolution,tripleArithmeticCoefficient_zero,tripleArithmeticCoefficient_one]

theorem tripleBudget_same_sign_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (r : ℕ) :
    ‖∫ t, ((tripleBudgetLogWeight ω T r (t/T)/T:ℝ):ℂ)*
      (pairPrimeSeries (X,t)*pairPrimeSeries (Y,t))‖ ≤
      triplePrimeMass X*triplePrimeMass Y*tripleBudgetOmega ω T r/(T*Real.log 4) := by
  have ht : 0<T := by linarith
  have he := tripleLog_linear_identity (tripleBudgetLogWeight ω T r)
    (tripleBudgetLogWeight_integrable ω hω T hT r) T ht (tripleLogConvolution X Y)
    (tripleLogConvolution_mass_summable X Y hX hY)
  simp_rw [tripleLogConvolution_series X Y _ hX hY] at he
  rw [he]
  have hb (n : LogGapIndex) :
      ‖tripleLogConvolution X Y n*pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ))
        (T/(2*Real.pi)*Real.log n.val)‖ ≤
      (tripleBudgetOmega ω T r/(T*Real.log 4))*‖tripleLogConvolution X Y n‖ := by
    by_cases hn : n.val<4
    · simp [tripleLogConvolution,tripleArithmeticConvolution_below_four X Y n.val hn]
    have hn4 : 4≤n.val := Nat.le_of_not_gt hn
    have hd := tripleLog_linear_decay (tripleBudgetLogWeight ω T r)
      ((tripleBudgetLogWeight_smooth ω hω T hT r).of_le (by simp))
      (tripleBudgetLogWeight_compact ω hω T r) T ht n
    have hl : Real.log 4≤Real.log (n.val:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn4)
    have hh := hd.trans (div_le_div_of_nonneg_left (fourierDerivativeL1_nonneg _ _)
      (mul_pos ht (Real.log_pos (by norm_num : (1:ℝ)<4))) (mul_le_mul_of_nonneg_left hl ht.le))
    rw [norm_mul,mul_comm (tripleBudgetOmega ω T r/(T*Real.log 4))]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
  have hm := (tripleLogConvolution_mass_summable X Y hX hY).mul_left
    (tripleBudgetOmega ω T r/(T*Real.log 4))
  have hh := tsum_of_norm_bounded hm.hasSum hb
  rw [tsum_mul_left] at hh
  apply hh.trans
  have hn : 0≤tripleBudgetOmega ω T r/(T*Real.log 4) :=
    div_nonneg (fourierDerivativeL1_nonneg _ _) (by positivity)
  convert mul_le_mul_of_nonneg_left (tripleLogConvolution_mass_bound X Y hX hY) hn using 1 <;> (try simp only [tripleLogMass]) <;> ring

end
end HigherCorrelations
