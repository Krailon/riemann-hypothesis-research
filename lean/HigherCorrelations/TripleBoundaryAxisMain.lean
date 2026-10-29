import HigherCorrelations.TripleBoundaryAxisAlgebra
import HigherCorrelations.TripleBoundaryAxisScales

/-! UNCONDITIONAL local axis leading-term comparison in exact project units. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_axis_main_bound (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T r s S : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hs : 0 ≤ s) (hsS : s ≤ S) :
    ‖(tripleRetainedMain ω T ((tripleTestBase T)^r) (Real.exp s):ℂ)/(Real.log T:ℂ)^2-
      ((r*(1+s)*Real.exp (-(2*s)):ℝ):ℂ)‖ ≤
      (1+S)*(Real.log (2*Real.pi)+Real.log 2+(1+Real.log 2)*S/2)/Real.log T+
      (1+2*(1+Real.log 2)*(1+S))*(1+Real.log T)*
        Real.exp (-(2*Real.log (tripleTestBase T)*r)) := by
  have ht := tripleBoundary_height T hT
  have hb := (tripleTestBase_bounds T ht.1).2.1
  have hc : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hμ := tripleSmoothingMean_bounds ω hω
  have ha : Real.exp (-(2*s)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h := tripleBoundary_axis_algebra (Real.log T) (Real.log (tripleTestBase T))
    (Real.log (2*Real.pi)) (tripleSmoothingMean ω) (Real.log 2) r s S
    (Real.exp (-(2*s))) (Real.exp (-(2*Real.log (tripleTestBase T)*r)))
    ht.2.1 hc ht.2.2.1 hμ.1 hμ.2 hr hr1 hs hsS (Real.exp_pos _).le ha (Real.exp_pos _).le
  have he : (tripleTestBase T)^r=Real.exp (Real.log (tripleTestBase T)*r) :=
    Real.rpow_def_of_pos (by linarith) _
  rw [he,tripleBoundary_axis_main]
  have he' : Real.exp (-(2*(Real.log (tripleTestBase T)*r+s))) =
      Real.exp (-(2*Real.log (tripleTestBase T)*r))*Real.exp (-(2*s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he']
  have heC : ∀ a q f : ℝ, ‖(a:ℂ)/(q:ℂ)^2-(f:ℂ)‖=|a/q^2-f| := by
    intro a q f
    rw [← Complex.ofReal_pow,← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [heC]
  simpa only [mul_assoc] using h

end
end HigherCorrelations
