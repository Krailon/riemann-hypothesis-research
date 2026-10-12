import HigherCorrelations.LocalZetaGrowth
import HigherCorrelations.LocalZeroCountDefinitions

/-! UNCONDITIONAL multiplicity mass bound on translated Jensen disks. -/
namespace HigherCorrelations
noncomputable section
open Metric Complex Real

theorem jensen_disk_geometry (t : ℝ) (ht : 4 ≤ |t|) (z : ℂ)
    (hz : z ∈ closedBall (jensenCenter t) (7/4)) :
    1/4 ≤ z.re ∧ 1 ≤ |z.im| ∧ ‖z‖ ≤ |t| + 4 := by
  have hn : ‖z - jensenCenter t‖ ≤ 7/4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := abs_re_le_norm (z - jensenCenter t)
  have hi := abs_im_le_norm (z - jensenCenter t)
  have hc : ‖jensenCenter t‖ ≤ 2+|t| := by
    simpa [jensenCenter, norm_mul, norm_real, Real.norm_eq_abs] using norm_add_le (2 : ℂ) (I*t)
  have ha := abs_add_le (z.im-t) t
  have hb := abs_add_le (t-z.im) z.im
  simp [jensenCenter] at hr hi
  dsimp [jensenCenter] at hn
  refine ⟨?_, ?_, ?_⟩
  · have := (abs_le.mp (hr.trans hn)).1; linarith
  · rw [abs_sub_comm] at hb
    have he : t-z.im+z.im=t := by ring
    rw [he] at hb
    linarith
  · have hh := norm_add_le (z-jensenCenter t) (jensenCenter t)
    rw [sub_add_cancel] at hh
    dsimp [jensenCenter] at hc hh
    linarith

theorem jensen_disk_analytic (t : ℝ) (ht : 4 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (jensenCenter t) (7/4)) := by
  intro z hz
  apply analyticOn_riemannZeta
  intro he
  have hh := (jensen_disk_geometry t ht z hz).2.1
  rw [Set.mem_singleton_iff.mp he] at hh
  norm_num at hh

theorem jensen_disk_norm_bound (t : ℝ) (ht : 4 ≤ |t|) (z : ℂ)
    (hz : z ∈ closedBall (jensenCenter t) (7/4)) :
    ‖riemannZeta z‖ ≤ 16*(|t|+2) := by
  obtain ⟨hre, him, hn⟩ := jensen_disk_geometry t ht z hz
  have hh := zeta_norm_le_quarter_strip hre him
  linarith [abs_nonneg t]

theorem localJensenMass_bound (t : ℝ) (ht : 4 ≤ |t|) :
    localJensenMass t ≤ (7 / Real.log (35/32)) * Real.log (|t|+2) := by
  have hc : riemannZeta (jensenCenter t) ≠ 0 := by
    intro h
    have := zeta_line_two_lower t
    rw [show 2+I*t=jensenCenter t from rfl, h, norm_zero] at this
    norm_num at this
  have hj := AnalyticOnNhd.sum_divisor_le (c := jensenCenter t) (r := (8/5 : ℝ))
    (R := (7/4 : ℝ)) (M := 16*(|t|+2)) (by norm_num) (by norm_num)
    (by have := abs_nonneg t; linarith) (by norm_num; exact jensen_disk_analytic t ht) hc
    (fun z hz => jensen_disk_norm_bound t ht z (sphere_subset_closedBall (by simpa only [abs_of_pos (by norm_num : (0:ℝ)<7/4)] using hz)))
  have hd : 0 < Real.log (35/32) := Real.log_pos (by norm_num)
  have hlog : Real.log (16*(|t|+2)/‖riemannZeta (jensenCenter t)‖) ≤
      7*Real.log (|t|+2) := by
    have hz := zeta_line_two_lower t
    change 1/4 ≤ ‖riemannZeta (jensenCenter t)‖ at hz
    have hp : 0 < ‖riemannZeta (jensenCenter t)‖ := by linarith
    have h₁ : 16*(|t|+2)/‖riemannZeta (jensenCenter t)‖ ≤ 64*(|t|+2) := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [abs_nonneg t]
    have h₂ : Real.log (2:ℝ) ≤ Real.log (|t|+2) :=
      Real.log_le_log (by norm_num) (by have := abs_nonneg t; linarith)
    have h₃ : Real.log (64*(|t|+2)) = 6*Real.log 2 + Real.log (|t|+2) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have hh := Real.log_pow (2 : ℝ) 6
      norm_num at hh
      rw [hh]
    exact (Real.log_le_log (by positivity) h₁).trans (by rw [h₃]; linarith)
  norm_num at hj
  have habs : |(8:ℝ)/5| = 8/5 := by norm_num
  rw [habs] at hj
  change localJensenMass t ≤ _ at hj
  convert hj.trans (div_le_div_of_nonneg_right hlog hd.le) using 1; ring

end
end HigherCorrelations
