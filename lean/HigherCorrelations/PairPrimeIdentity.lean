import HigherCorrelations.PairEulerContour
import HigherCorrelations.PairPrimeConvergence

/-! The right-contour integral plus the right kernel-pole contribution is exactly -P.
UNCONDITIONAL. The knots X=n+1 are included without a half-weight convention. -/
namespace HigherCorrelations
noncomputable section

theorem pairEulerTerm_add_one (n : ℕ) (z : ℂ) :
    pairEulerTerm n (z+1) = pairEulerTerm n z / (n+1:ℂ) := by
  unfold pairEulerTerm
  have he : (Real.log (n+1:ℝ):ℂ)*(-(z+1)) =
      (Real.log (n+1:ℝ):ℂ)*(-z) - (Real.log (n+1:ℝ):ℂ) := by ring
  rw [he, Complex.exp_sub]
  rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
  push_cast
  ring

theorem pairPrimeTerm_eq_euler (n : ℕ) (p : ℝ × ℝ) :
    pairPrimeTerm n p = pairEulerTerm n (pairSpectralPoint p.2) *
      (min ((n+1:ℝ)/p.1) (p.1/(n+1:ℝ)) : ℝ) := by
  unfold pairPrimeTerm pairEulerTerm pairSpectralPoint
  congr 3
  ring

theorem pairMellin_weight (X a : ℝ) (hX : 0 < X) (ha : 0 < a) :
    pairedMellinKernel (X/a) - (X/a:ℝ) = -(min (a/X) (X/a):ℝ) := by
  by_cases h : a < X
  · have hh : 1 < X/a := (one_lt_div ha).mpr h
    rw [pairedMellinKernel_gt_one _ hh]
    have hm : a/X ≤ X/a := by
      rw [div_le_div_iff₀ hX ha]
      nlinarith
    rw [min_eq_left hm]
    push_cast
    rw [inv_div]
    ring
  · have hx : X ≤ a := le_of_not_gt h
    rw [pairedMellinKernel_le_one _ (div_pos hX ha) ((div_le_one ha).mpr hx)]
    have hm : X/a ≤ a/X := by
      rw [div_le_div_iff₀ ha hX]
      nlinarith
    rw [min_eq_right hm]
    simp

theorem pairPrimeTerm_contour_identity (n : ℕ) (X t : ℝ) (hX : 0 < X) :
    pairEulerTerm n (pairSpectralPoint t) * pairedMellinKernel (X/(n+1)) -
      (X:ℂ) * pairEulerTerm n (pairSpectralPoint t+1) = -pairPrimeTerm n (X,t) := by
  rw [pairEulerTerm_add_one, pairPrimeTerm_eq_euler]
  have hw := pairMellin_weight X (n+1) hX (by positivity)
  push_cast at hw
  calc
    _ = pairEulerTerm n (pairSpectralPoint t) *
      (pairedMellinKernel (X/(n+1)) - (X:ℂ)/(n+1:ℂ)) := by ring
    _ = _ := by rw [hw]; ring

theorem pairRightIntegral_prime_identity (X t : ℝ) (hX : 1 ≤ X) :
    pairRightIntegral (X,t) + (X:ℂ) *
      (deriv riemannZeta (pairSpectralPoint t+1) / riemannZeta (pairSpectralPoint t+1)) =
      -pairPrimeSeries (X,t) := by
  have hs : 1 < (pairSpectralPoint t+1).re := by norm_num [pairSpectralPoint]
  have he := ((pairEulerTerm_summable _ hs).hasSum.mul_left (X:ℂ))
  rw [pairEulerSeries _ hs] at he
  have hi := (pairRightIntegral_hasSum X t (by linarith)).sub he
  simp_rw [pairPrimeTerm_contour_identity _ X t (by linarith)] at hi
  have hp := ((pairPrimeTerm_summable X t hX).of_norm.hasSum).neg
  have hh := hi.unique hp
  simpa only [pairPrimeSeries, neg_div, mul_neg, sub_neg_eq_add] using hh

end
end HigherCorrelations
