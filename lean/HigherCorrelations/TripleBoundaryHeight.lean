import HigherCorrelations.TripleBoundaryDefinitions
import HigherCorrelations.TripleBoundaryArch
import HigherCorrelations.TripleTestGeometry

/-! UNCONDITIONAL height comparisons, uniform down to T = 2 pi e. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundaryLogConstant_pos : 0<tripleBoundaryLogConstant := by
  have hp := Real.pi_gt_three
  have h1 := Real.log_pos (show 1<2*Real.pi by linarith)
  have h2 := Real.log_pos (show (1:ℝ)<3 by norm_num)
  unfold tripleBoundaryLogConstant
  linarith

theorem tripleBoundary_height (T : ℝ) (hT : 2*Real.pi*Real.exp 1≤T) :
    2*Real.pi<T ∧ 1≤Real.log (tripleTestBase T) ∧
    Real.log T=Real.log (tripleTestBase T)+Real.log (2*Real.pi) ∧
    Real.log (2*T+2)≤tripleBoundaryLogConstant*Real.log (tripleTestBase T) := by
  have hp : 0<2*Real.pi := by positivity
  have he : 1<Real.exp 1 := by simpa using Real.exp_lt_exp.mpr (show (0:ℝ)<1 by norm_num)
  have hT' : 2*Real.pi<T := by nlinarith
  have ht := tripleTestBase_bounds T hT'
  have hT0 : 0<T := by linarith [ht.1]
  have hb : Real.exp 1≤tripleTestBase T := (le_div_iff₀ hp).mpr (by nlinarith [hT])
  have hb1 : 1≤Real.log (tripleTestBase T) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hb
    simpa using hh
  have heq : Real.log T=Real.log (tripleTestBase T)+Real.log (2*Real.pi) := by
    rw [tripleTestBase,Real.log_div hT0.ne' hp.ne']
    ring
  refine ⟨hT',hb1,heq,?_⟩
  have hlog := (tripleBoundary_log_difference T ht.1).2
  have hconst : 0≤Real.log (2*Real.pi)+Real.log 3 := by
    exact add_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))
      (Real.log_nonneg (by norm_num))
  have hh := mul_le_mul_of_nonneg_left hb1 hconst
  unfold tripleBoundaryLogConstant
  rw [heq] at hlog
  nlinarith only [hlog,hh]

theorem tripleBoundary_height_cube (T : ℝ) (hT : 3≤T) :
    Real.log (2*T+2)^3/T≤81 := by
  have ht : 0<T := by linarith
  have hx : 0<2*T+2 := by linarith
  have hl : 0≤Real.log (2*T+2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2*T+2)≤3*(2*T+2)^(1/3:ℝ) := by
    have hh := Real.log_le_rpow_div hx.le (show (0:ℝ)<1/3 by norm_num)
    linarith
  have hh := pow_le_pow_left₀ hl hlog 3
  rw [mul_pow,← Real.rpow_natCast ((2*T+2)^(1/3:ℝ)),← Real.rpow_mul hx.le] at hh
  norm_num at hh
  apply (div_le_iff₀ ht).mpr
  nlinarith

end
end HigherCorrelations
