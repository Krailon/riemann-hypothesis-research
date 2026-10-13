import HigherCorrelations.PairedMellinDefinitions
import Mathlib.Analysis.MellinInversion

/-! UNCONDITIONAL transform of the continuous paired seed, including its knot. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped Topology

theorem pairedMellinSeed_transform (s : ℂ) (hs : 1 < s.re) :
    HasMellin pairedMellinSeed s (pairedMellinSymbol s) := by
  have h₁ := hasMellin_cpow_Ioc (-1) (s := s) (by simpa using sub_pos.mpr hs)
  have h₂ := hasMellin_cpow_Ioc 1 (s := s) (by simp; linarith)
  have h := hasMellin_sub h₁.1 h₂.1
  rw [h₁.2,h₂.2] at h
  have hf : (fun x : ℝ => indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ)^(-1 : ℂ)) x -
      indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ)^(1 : ℂ)) x) = pairedMellinSeed := by
    funext x
    by_cases hx : x ∈ Ioc (0:ℝ) 1 <;> simp [pairedMellinSeed, hx, Complex.cpow_neg_one]
  rw [hf] at h
  convert h using 1
  unfold pairedMellinSymbol
  have hm : s-1 ≠ 0 := by intro hh; have := congrArg Complex.re hh; simp at this; linarith
  have hp : s+1 ≠ 0 := by intro hh; have := congrArg Complex.re hh; simp at this; linarith
  have hd : s^2-1 ≠ 0 := by
    rw [show s^2-1=(s-1)*(s+1) by ring]
    exact mul_ne_zero hm hp
  simp only [← sub_eq_add_neg]
  field_simp
  ring

theorem pairedMellinSeed_positive (x : ℝ) (hx : 0<x) :
    pairedMellinSeed x = (max (x⁻¹-x) 0 : ℝ) := by
  by_cases h : x≤1
  · have hh : 0≤x⁻¹-x := by
      have hp : 0≤(x⁻¹-x)*x := by rw [sub_mul, inv_mul_cancel₀ hx.ne']; nlinarith
      exact nonneg_of_mul_nonneg_left hp hx
    simp [pairedMellinSeed, hx, h, max_eq_left hh, Complex.ofReal_sub, Complex.ofReal_inv]
  · have hh : x⁻¹-x ≤ 0 := by
      have hp : (x⁻¹-x)*x ≤ 0 := by rw [sub_mul, inv_mul_cancel₀ hx.ne']; nlinarith
      exact nonpos_of_mul_nonpos_left hp hx
    simp [pairedMellinSeed, h, max_eq_right hh]

theorem pairedMellinSeed_continuous (x : ℝ) (hx : 0<x) :
    ContinuousAt pairedMellinSeed x := by
  have h : ContinuousAt (fun x : ℝ => (max (x⁻¹-x) 0 : ℝ)) x :=
    ((continuousAt_id.inv₀ hx.ne').sub continuousAt_id).max continuousAt_const
  have hc := Complex.continuous_ofReal.continuousAt.comp h
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact pairedMellinSeed_positive y hy

theorem pairedMellinSeed_at_one : pairedMellinSeed 1 = 0 := by
  simp [pairedMellinSeed]

end
end HigherCorrelations
