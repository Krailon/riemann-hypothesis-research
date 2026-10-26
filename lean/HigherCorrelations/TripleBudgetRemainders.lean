import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.PairUniformFormula
import HigherCorrelations.TripleExpansion

/-! UNCONDITIONAL four separately named remainder bounds on the center window. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleBudgetRemainderBound_nonneg (j : PairRemainderKind) (T x : ℝ)
    (hT : 3≤T) (hx : 1≤x) : 0 ≤ tripleBudgetRemainderBound j T x := by
  have ha : 0≤pairArchConstant := by
    have h := (norm_nonneg (pairArchError (1,0))).trans (pairArchError_bound 1 0 (by norm_num))
    simpa using h
  have hd := pairDSConstant_nonneg
  cases j <;> simp only [tripleBudgetRemainderBound] <;> positivity

theorem tripleBudget_remainder_bound (j : PairRemainderKind) (T x t : ℝ)
    (hT : 3≤T) (hx : 1≤x) (ht : t ∈ Icc T (2*T)) :
    ‖pairRHSRemainder j x t‖ ≤ tripleBudgetRemainderBound j T x := by
  have ht0 : 0≤t := by linarith [ht.1]
  cases j
  · exact pairArchError_bound x t hx
  · exact pairDSError_bound x t hx
  · have h := pairPoleCorrection_bound x t hx
    rw [← Real.sqrt_eq_rpow] at h
    exact h.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [ht.1]))
  · have h := pairTrivialCorrection_bound x t hx
    rw [abs_of_nonneg ht0] at h
    exact h.trans (div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith [ht.1]))

theorem tripleBudget_remainder_total_bound (T x t : ℝ)
    (hT : 3≤T) (hx : 1≤x) (ht : t ∈ Icc T (2*T)) :
    ‖tripleComponent .H x t‖ ≤ tripleBudgetRemainderTotal T x := by
  change ‖∑ j, pairRHSRemainder j x t‖ ≤ ∑ j, tripleBudgetRemainderBound j T x
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ =>
    tripleBudget_remainder_bound j T x t hT hx ht))

theorem tripleBudget_arch_bound (T x t : ℝ)
    (hT : 3≤T) (hx : 1≤x) (ht : t ∈ Icc T (2*T)) :
    ‖tripleComponent .A x t‖ ≤ tripleBudgetAlpha T x := by
  have ht0 : 0≤t := by linarith [ht.1]
  have hl : 0≤Real.log (t+2) := Real.log_nonneg (by linarith)
  simp only [tripleComponent,tripleArch,abs_of_nonneg ht0,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (div_nonneg hl (by linarith : 0≤x)),tripleBudgetAlpha]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith [ht.2])) (by linarith)

end
end HigherCorrelations
