import HigherCorrelations.PairRHSArchIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! UNCONDITIONAL compact-interval L2 estimates. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairRHSL2_memLp (f : ℝ → ℂ) (T : ℝ)
    (hf : ContinuousOn f (Set.Icc 0 T)) : MemLp f 2 (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable measurableSet_Icc) C
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC t ht))

theorem pairRHSL2_cauchy (f g : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Set.Icc 0 T)) (hg : ContinuousOn g (Set.Icc 0 T)) :
    |(∫ t in (0:ℝ)..T, f t*star (g t)).re| ≤ pairRHSL2 f T*pairRHSL2 g T := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp f (ENNReal.ofReal 2) (volume.restrict (Set.Icc 0 T)) by
      simpa using pairRHSL2_memLp f T hf)
    (show MemLp g (ENNReal.ofReal 2) (volume.restrict (Set.Icc 0 T)) by
      simpa using pairRHSL2_memLp g T hg)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT] at h
  calc
    _ ≤ ‖∫ t in (0:ℝ)..T, f t*star (g t)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ t in (0:ℝ)..T, ‖f t‖*‖g t‖ := by
      simpa only [norm_mul,norm_star] using intervalIntegral.norm_integral_le_integral_norm hT
        (f := fun t => f t*star (g t))
    _ ≤ _ := by simpa only [pairRHSL2, Real.sqrt_eq_rpow] using h

theorem pairRHSL2_square_bound (f : ℝ → ℂ) (T B : ℝ) (hB : 0 ≤ B)
    (hb : (∫ t in (0:ℝ)..T, ‖f t‖^2) ≤ B^2) : pairRHSL2 f T ≤ B :=
  (Real.sqrt_le_left hB).mpr hb

end
end HigherCorrelations
