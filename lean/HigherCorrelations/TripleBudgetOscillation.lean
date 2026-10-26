import HigherCorrelations.TripleBudgetLogWeight
import HigherCorrelations.TripleMixedFourier
import HigherCorrelations.PairMeanFourierDecay

/-! UNCONDITIONAL oscillatory smoothing bounds, with literal 2 pi cancellation.
The compact zero extension supplies all endpoint vanishing. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetLogWeight_eq_abs (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤T) (r : ℕ) (u : ℝ) :
    tripleBudgetLogWeight ω T r u = ω u*Real.log (|T*u|+2)^r := by
  by_cases hu : ω u=0
  · simp [tripleBudgetLogWeight,hu]
  · have hs := tripleBudgetWeight_support ω hω hu
    simp only [tripleBudgetLogWeight,abs_of_nonneg (mul_nonneg hT (by linarith [hs.1] : 0≤u))]

theorem tripleBudgetLogWeight_integrable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) : Integrable (tripleBudgetLogWeight ω T r) :=
  (tripleBudgetLogWeight_smooth ω hω T hT r).continuous.integrable_of_hasCompactSupport
    (tripleBudgetLogWeight_compact ω hω T r)

theorem tripleBudgetLogWeight_integral (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤T) (r : ℕ) :
    (∫ u, tripleBudgetLogWeight ω T r u) = tripleBudgetMoment ω T r := by
  simp_rw [tripleBudgetLogWeight_eq_abs ω hω T hT r]
  rfl

theorem tripleBudgetLogWeight_zero (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 0≤T) (r : ℕ) :
    pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ)) 0 = (tripleBudgetMoment ω T r:ℂ) := by
  rw [pairMeanFourier_zero,integral_complex_ofReal,tripleBudgetLogWeight_integral ω hω T hT r]

theorem tripleBudgetLogWeight_decay (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) (r : ℕ) (v : ℝ) (hv : v≠0) :
    ‖pairMeanFourier (fun u => (tripleBudgetLogWeight ω T r u:ℂ)) (T/(2*Real.pi)*v)‖ ≤
      tripleBudgetOmega ω T r/(T*|v|) := by
  have ht : 0<T := by linarith
  have hb := fourierDecay_real_bound (tripleBudgetLogWeight ω T r) 1
    ((tripleBudgetLogWeight_smooth ω hω T hT r).of_le (by simp))
    (tripleBudgetLogWeight_compact ω hω T r) (T/(2*Real.pi)*v)
    (mul_ne_zero (div_ne_zero ht.ne' (by positivity)) hv)
  have he : 2*Real.pi*|T/(2*Real.pi)*v|=T*|v| := by
    rw [abs_mul,abs_div,abs_of_pos ht,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  simpa only [pow_one,he,tripleBudgetOmega] using hb

end
end HigherCorrelations
