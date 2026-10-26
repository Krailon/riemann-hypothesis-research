import HigherCorrelations.TripleArithmeticFourier
import HigherCorrelations.TripleBudgetOscillation
import HigherCorrelations.PairRHSPrimeWeight

/-! UNCONDITIONAL linear Fourier passage and same-sign prime smoothing bounds. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairMeanWeighted_linear_identity {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (c : ι → ℂ) (hc : Summable (fun n => ‖c n‖))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∫ t, M t*pairFrequencySum μ c t) = ∑' n, c n*pairMeanFourier M (-μ n) := by
  let G : ι → ℝ → ℂ := fun n t => M t*(c n*pairMeanCharacter (μ n*t))
  have hG (n) : Integrable (G n) := pairMeanWeightedTerm_integrable M hM _ _
  have hL1 : Summable (fun n => ∫ t, ‖G n t‖) := by
    have he (n : ι) : (∫ t, ‖G n t‖) = (∫ t, ‖M t‖)*‖c n‖ := by
      simp only [G,norm_mul,pairMeanCharacter_norm,mul_one]
      exact integral_mul_const _ _
    simp_rw [he]
    exact hc.mul_left _
  calc
    _ = ∫ t, ∑' n, G n t := by simp only [G,pairFrequencySum,tsum_mul_left]
    _ = ∑' n, ∫ t, G n t := (integral_tsum_of_summable_integral_norm hG hL1).symm
    _ = _ := by simp only [G,pairMeanWeightedTerm_integral]

theorem tripleLog_linear_identity (φ : ℝ → ℝ) (hφ : Integrable φ)
    (T : ℝ) (hT : 0<T) (c : LogGapIndex → ℂ) (hc : Summable (fun n => ‖c n‖)) :
    (∫ t, ((φ (t/T)/T:ℝ):ℂ)*pairFrequencySum tripleLogFrequency c t) =
      ∑' n, c n*pairMeanFourier (fun u => (φ u:ℂ)) (T/(2*Real.pi)*Real.log n.val) := by
  rw [pairMeanWeighted_linear_identity tripleLogFrequency c hc (fun t => ((φ (t/T)/T:ℝ):ℂ))
    ((hφ.comp_div hT.ne').div_const T).ofReal]
  apply tsum_congr
  intro n
  rw [pairMeanFourier_normalized φ T _ hT]
  unfold tripleLogFrequency
  congr 2
  ring

theorem tripleLog_linear_decay (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (T : ℝ) (hT : 0<T) (n : LogGapIndex) :
    ‖pairMeanFourier (fun u => (φ u:ℂ)) (T/(2*Real.pi)*Real.log n.val)‖ ≤
      fourierDerivativeL1 φ 1/(T*Real.log n.val) := by
  have hn : 0<Real.log (n.val:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n.val by have := n.property; omega))
  have he : 2*Real.pi*|T/(2*Real.pi)*Real.log n.val|=T*Real.log n.val := by
    rw [abs_of_pos (by positivity : 0<T/(2*Real.pi)*Real.log n.val)]
    field_simp
  simpa only [pow_one,he] using fourierDecay_real_bound φ 1 hφ hs
    (T/(2*Real.pi)*Real.log n.val) (by positivity)

theorem tripleLogCoefficient_div_log_summable (x : ℝ) (hx : 1≤x) :
    Summable (fun n : LogGapIndex => tripleArithmeticCoefficient x n.val/Real.log n.val) := by
  have hn : Summable (fun n : ℕ => tripleArithmeticCoefficient x n/Real.log n) :=
    (summable_nat_add_iff 1).mp (by simpa only [tripleArithmeticCoefficient_succ,Nat.cast_add,Nat.cast_one]
      using pairRHS_coefficient_div_log_summable x hx)
  exact hn.comp_injective Subtype.val_injective

theorem tripleLogCoefficient_div_log_bound (x : ℝ) (hx : 1≤x) :
    (∑' n : LogGapIndex, tripleArithmeticCoefficient x n.val/Real.log n.val) ≤ 5*Real.sqrt x := by
  rw [tripleNat_tsum_ge_two (fun n => tripleArithmeticCoefficient x n/Real.log n)
    (by simp [tripleArithmeticCoefficient_zero]) (by simp [tripleArithmeticCoefficient_one])]
  have hn : Summable (fun n : ℕ => tripleArithmeticCoefficient x n/Real.log n) :=
    (summable_nat_add_iff 1).mp (by simpa only [tripleArithmeticCoefficient_succ,Nat.cast_add,Nat.cast_one]
      using pairRHS_coefficient_div_log_summable x hx)
  rw [hn.tsum_eq_zero_add]
  simpa only [tripleArithmeticCoefficient_zero,zero_div,zero_add,tripleArithmeticCoefficient_succ,Nat.cast_add,Nat.cast_one]
    using pairRHS_coefficient_div_log_sum x hx

theorem tripleBudget_single_prime_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤T) (hx : 1≤x) (r : ℕ) :
    ‖∫ t, ((tripleBudgetLogWeight ω T r (t/T)/T:ℝ):ℂ)*pairPrimeSeries (x,t)‖ ≤
      5*Real.sqrt x*tripleBudgetOmega ω T r/T := by
  have ht : 0<T := by linarith
  have he := tripleLog_linear_identity (tripleBudgetLogWeight ω T r)
    (tripleBudgetLogWeight_integrable ω hω T hT r) T ht (tripleLogCoefficient x)
    (tripleLogCoefficient_mass_summable x hx)
  simp_rw [tripleLogCoefficient_series x _ hx] at he
  rw [he]
  have hb (n : LogGapIndex) :
      ‖tripleLogCoefficient x n*pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ))
        (T/(2*Real.pi)*Real.log n.val)‖ ≤
      (tripleBudgetOmega ω T r/T)*(tripleArithmeticCoefficient x n.val/Real.log n.val) := by
    rw [norm_mul]
    have hd := tripleLog_linear_decay (tripleBudgetLogWeight ω T r)
      ((tripleBudgetLogWeight_smooth ω hω T hT r).of_le (by simp))
      (tripleBudgetLogWeight_compact ω hω T r) T ht n
    have hh := mul_le_mul_of_nonneg_left hd (tripleArithmeticCoefficient_nonneg x hx n.val)
    simpa only [tripleLogCoefficient,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (tripleArithmeticCoefficient_nonneg x hx n.val),tripleBudgetOmega] using
      (show tripleArithmeticCoefficient x n.val*‖pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ))
        (T/(2*Real.pi)*Real.log n.val)‖ ≤
        (fourierDerivativeL1 (tripleBudgetLogWeight ω T r) 1/T)*(tripleArithmeticCoefficient x n.val/Real.log n.val) by
          convert hh using 1 <;> ring)
  have hm := (tripleLogCoefficient_div_log_summable x hx).mul_left (tripleBudgetOmega ω T r/T)
  have hb' := tsum_of_norm_bounded hm.hasSum hb
  rw [tsum_mul_left] at hb'
  apply hb'.trans
  have hn : 0≤tripleBudgetOmega ω T r/T := div_nonneg (fourierDerivativeL1_nonneg _ _) ht.le
  convert mul_le_mul_of_nonneg_left (tripleLogCoefficient_div_log_bound x hx) hn using 1 <;> ring

end
end HigherCorrelations
