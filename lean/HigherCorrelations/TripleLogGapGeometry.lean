import HigherCorrelations.PairSieveGeometry
import Mathlib.NumberTheory.Harmonic.Bounds

/-! UNCONDITIONAL geometric inputs for the absolute reciprocal-log budget.
The diagonal is excluded before division. Comparable-ratio endpoints are closed. -/
namespace HigherCorrelations
noncomputable section

theorem tripleLogGap_nonzero (m n : ℝ) (hm : 0<m) (hn : 0<n) (hne : m≠n) :
    0 < |Real.log (m/n)| := by
  apply abs_pos.mpr
  intro he
  exact hne ((div_eq_one_iff_eq hn.ne').mp (Real.eq_one_of_pos_of_log_eq_zero (by positivity) he))

theorem tripleLogGap_inverse (m n : ℝ) (hm : 0<m) (hn : 0<n) (hne : m≠n) :
    1/|Real.log (m/n)| ≤ max m n/|m-n| := by
  apply (div_le_div_iff₀ (tripleLogGap_nonzero m n hm hn hne) (abs_pos.mpr (sub_ne_zero.mpr hne))).mpr
  simpa using pairSieve_log_distance m n hm hn

theorem tripleLogGap_far (m n : ℝ) (hm : 0<m) (hn : 0<n)
    (hfar : n<m/2 ∨ 2*m<n) : 1/|Real.log (m/n)| ≤ 1/Real.log 2 := by
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ |Real.log (m/n)| := by
    rcases hfar with h | h
    · exact (Real.log_le_log (by norm_num) ((le_div_iff₀ hn).mpr (by linarith))).trans (le_abs_self _)
    · have he : Real.log (n/m) = -Real.log (m/n) := by
        rw [Real.log_div hn.ne' hm.ne',Real.log_div hm.ne' hn.ne']; ring
      have hb := Real.log_le_log (by norm_num : (0:ℝ)<2)
        ((le_div_iff₀ hm).mpr (by linarith : 2*m≤n))
      rw [he] at hb
      exact hb.trans (neg_le_abs _)
  exact one_div_le_one_div_of_le hp hl

theorem tripleLogGap_comparable_max (m n : ℝ) (hm : 0<m) (hn : 0<n)
    (hlo : m/2≤n) (hhi : n≤2*m) : max m n ≤ Real.sqrt 2 * Real.sqrt m * Real.sqrt n := by
  have hsq : (max m n)^2 ≤ 2*m*n := by
    rcases le_total n m with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]; nlinarith
  have he : (Real.sqrt 2 * Real.sqrt m * Real.sqrt n)^2 = 2*m*n := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt hm.le,Real.sq_sqrt hn.le]
  have hh : 0 ≤ Real.sqrt 2 * Real.sqrt m * Real.sqrt n := by positivity
  nlinarith

theorem tripleLogGap_comparable (m n : ℝ) (hm : 0<m) (hn : 0<n) (hne : m≠n)
    (hlo : m/2≤n) (hhi : n≤2*m) :
    1/|Real.log (m/n)| ≤ Real.sqrt 2 * Real.sqrt m * Real.sqrt n/|m-n| :=
  (tripleLogGap_inverse m n hm hn hne).trans
    (div_le_div_of_nonneg_right (tripleLogGap_comparable_max m n hm hn hlo hhi) (abs_nonneg _))

end
end HigherCorrelations
