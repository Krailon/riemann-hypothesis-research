import HigherCorrelations.TripleBudgetL2
import HigherCorrelations.PairPrimeMean

/-! UNCONDITIONAL weighted prime norms. The mean-square branch includes x=2T;
the coefficient mass supplies a bound for every x>=1. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetPrime_sup_mass (x t : ℝ) (hx : 1≤x) :
    ‖pairPrimeSeries (x,t)‖ ≤ triplePrimeMass x := by
  rw [pairMeanPrimeSeries_frequency]
  have h := pairFrequencySum_bound pairMeanPrimeFrequency (fun n => (pairMeanPrimeCoefficient x n:ℂ))
    (pairMeanPrimeCoefficient_summable x hx) t
  simpa only [triplePrimeMass,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pairMeanPrimeCoefficient_nonneg x hx _)] using h

theorem tripleBudgetPrimeL2_mass (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T x : ℝ) (hT : 3≤T) (hx : 1≤x) : tripleBudgetPrimeL2 ω T x ≤ triplePrimeMass x := by
  exact tripleBudgetL2_sup ω hω T (by linarith) _ (pairRHS_prime_continuous x hx) _
    (tsum_nonneg (pairMeanPrimeCoefficient_nonneg x hx)) (fun t _ => tripleBudgetPrime_sup_mass x t hx)

theorem tripleBudgetPrime_weighted_square (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (W T x : ℝ) (hW : 0≤W) (hωW : ∀ u, ω u≤W) (hT : 3≤T) (hx : 1≤x) :
    (∫ t : ℝ, ω (t/T)/T*‖pairPrimeSeries (x,t)‖^2) ≤ (W/T)*pairPrimeMeanSquare x (2*T) := by
  have hT0 : 0<T := by linarith
  have hc := (pairRHS_prime_continuous x hx).norm.pow 2
  have hi : IntegrableOn (fun t => ‖pairPrimeSeries (x,t)‖^2) (Icc (0:ℝ) (2*T)) :=
    hc.continuousOn.integrableOn_Icc
  have hupper : Integrable (fun t => (W/T)*(Icc (0:ℝ) (2*T)).indicator (fun t => ‖pairPrimeSeries (x,t)‖^2) t) :=
    (hi.integrable_indicator measurableSet_Icc).const_mul _
  have hpoint (t : ℝ) : ω (t/T)/T*‖pairPrimeSeries (x,t)‖^2 ≤
      (W/T)*(Icc (0:ℝ) (2*T)).indicator (fun t => ‖pairPrimeSeries (x,t)‖^2) t := by
    by_cases ht : t ∈ Icc (0:ℝ) (2*T)
    · rw [indicator_of_mem ht]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hωW _) hT0.le) (sq_nonneg _)
    · have hz : ω (t/T)=0 := by
        by_contra hn
        have hs := tripleMaster_support ω (tripleBudgetWeight_support ω hω) T hT0 hn
        exact ht ⟨by linarith [hs.1],hs.2⟩
      simp [indicator_of_notMem ht,hz]
  have hb := integral_mono (tripleBudget_weighted_integrable ω hω T hT0 _ hc) hupper hpoint
  simpa only [Pi.pow_apply,integral_const_mul,integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : (0:ℝ)≤2*T),
    pairPrimeMeanSquare] using hb

theorem tripleBudgetPrimeL2_uniform : ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω →
    ∀ W T x : ℝ, 0≤W → (∀ u, ω u≤W) → 3≤T → 1≤x → x≤2*T →
      tripleBudgetPrimeL2 ω T x ≤ Real.sqrt (2*C*W*Real.log (2*x)) := by
  obtain ⟨C,hC,hb⟩ := pairPrimeMeanSquare_upper
  refine ⟨C,hC,?_⟩
  intro ω hω W T x hW hωW hT hx hxT
  have h := tripleBudgetPrime_weighted_square ω hω W T x hW hωW hT hx
  have hp := mul_le_mul_of_nonneg_left (hb x (2*T) hx (by linarith) hxT)
    (div_nonneg hW (by linarith : 0≤T))
  have he : W/T*(C*(2*T*Real.log (2*x))) = 2*C*W*Real.log (2*x) := by
    field_simp
  rw [he] at hp
  exact Real.sqrt_le_sqrt (h.trans hp)

end
end HigherCorrelations
