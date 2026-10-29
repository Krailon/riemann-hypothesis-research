import HigherCorrelations.TripleBudgetMoments
import HigherCorrelations.TripleBudgetInteriorPrimitives

/-! UNCONDITIONAL sharper archimedean cubic remainder. The loss is two
powers of log height, retaining the full inverse square of the product. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBoundary_log_difference (T : ℝ) (hT : 3≤T) :
    0≤Real.log (2*T+2)-Real.log T ∧
    Real.log (2*T+2)-Real.log T≤Real.log 3 := by
  have ht : 0<T := by linarith
  have hlo : Real.log T≤Real.log (2*T+2) := Real.log_le_log ht (by linarith)
  have hhi := Real.log_le_log (by linarith : 0<2*T+2) (show 2*T+2≤3*T by linarith)
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) ht.ne'] at hhi
  constructor <;> linarith

theorem tripleBoundary_archcube (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) :
    ‖tripleBudgetError ω T X Y .archcube‖ ≤
      (3*Real.log 3)*Real.log (2*T+2)^2/(X*Y)^2 := by
  apply (tripleBudget_archcube_bounds ω hω T X Y hT).2.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  let L := Real.log (2*T+2)
  let q := Real.log T
  have hq : 0≤q := Real.log_nonneg (by linarith)
  have h := tripleBoundary_log_difference T hT
  have hqL : q≤L := by dsimp [q,L]; linarith [h.1]
  have hL : 0≤L := hq.trans hqL
  have hh : L^2+L*q+q^2≤3*L^2 := by nlinarith [sq_nonneg (L-q)]
  have hp := mul_le_mul h.2 hh (by positivity : 0≤L^2+L*q+q^2)
    (Real.log_nonneg (by norm_num : (1:ℝ)≤3))
  change L^3-q^3 ≤ _
  convert hp using 1 <;> dsimp [L,q] <;> ring

end
end HigherCorrelations
