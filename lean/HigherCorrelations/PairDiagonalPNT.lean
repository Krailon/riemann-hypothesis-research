import PrimeNumberTheoremAnd.StrongPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! UNCONDITIONAL. A global logarithm-weighted PNT remainder.
The constants are existential; this file makes no numerical-effectivity claim. -/
namespace HigherCorrelations
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem pairDiagonalPNT_damping (c : ℝ) (hc : 0 < c) :
    Tendsto (fun u : ℝ => Real.log u * Real.exp (-c*(Real.log u)^(1/2:ℝ)))
      atTop (nhds 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).comp Real.tendsto_log_atTop)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
  have hl := Real.log_nonneg hu
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hl]
  norm_num

/-- Uniform for every real u>=1, including the compact initial range. -/
theorem pairDiagonalPNT_log_error : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ u →
    |Chebyshev.psi u-u| *Real.log u ≤ C*u := by
  obtain ⟨c,hc,hpnt⟩ := StrongPNT
  obtain ⟨K,hK,hbound⟩ := Asymptotics.isBigO_iff'.mp hpnt
  have hd := (pairDiagonalPNT_damping c hc).eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hbound.and hd)
  let R := max U 2
  let B := (Real.log 4+5)*Real.log R
  refine ⟨K+B+1, ?_, ?_⟩
  · have hR : 1 ≤ R := by dsimp [R]; have := le_max_right U (2:ℝ); linarith
    have hlR := Real.log_nonneg hR
    have : 0 ≤ B := by dsimp [B]; positivity
    linarith
  intro u hu
  have hu0 : 0 < u := by linarith
  have hl := Real.log_nonneg hu
  have hR : 1 ≤ R := by dsimp [R]; have := le_max_right U (2:ℝ); linarith
  have hlR := Real.log_nonneg hR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  by_cases hlarge : R ≤ u
  · obtain ⟨hb,hd⟩ := hU u ((le_max_left U 2).trans hlarge)
    change ‖Chebyshev.psi u-u‖ ≤ K*‖u*Real.exp (-c*(Real.log u)^(1/2:ℝ))‖ at hb
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)] at hb
    calc
      _ ≤ K*(u*Real.exp (-c*(Real.log u)^(1/2:ℝ)))*Real.log u := mul_le_mul_of_nonneg_right hb hl
      _ = K*u*(Real.log u*Real.exp (-c*(Real.log u)^(1/2:ℝ))) := by ring
      _ ≤ K*u*1 := mul_le_mul_of_nonneg_left hd.le (by positivity)
      _ ≤ _ := by nlinarith
  · have hpsi := Chebyshev.psi_le_const_mul_self hu0.le
    have hp0 := Chebyshev.psi_nonneg u
    have habs : |Chebyshev.psi u-u| ≤ (Real.log 4+5)*u := by
      apply abs_le.mpr
      constructor <;> nlinarith [Real.log_nonneg (show (1:ℝ)≤4 by norm_num)]
    have hlog : Real.log u ≤ Real.log R := Real.log_le_log hu0 (le_of_not_ge hlarge)
    calc
      _ ≤ ((Real.log 4+5)*u)*Real.log R := mul_le_mul habs hlog hl (by positivity)
      _ = B*u := by dsimp [B]; ring
      _ ≤ _ := by nlinarith

end
end HigherCorrelations
