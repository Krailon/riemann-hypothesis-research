import HigherCorrelations.TripleQuadrantAsymptotic

/-! UNCONDITIONAL scalar decay and uniform-limit assembly for local profiles. -/
namespace HigherCorrelations
noncomputable section
open Filter Set
open scoped Topology

theorem tripleBoundary_inverse_log_limit :
    Tendsto (fun T : ℝ => 1/Real.log T) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop Real.tendsto_log_atTop

theorem tripleBoundary_height_log_decay :
    Tendsto (fun T : ℝ => Real.log (2*T+2)^4/T) atTop (𝓝 0) := by
  have h := (tripleTest_envelope_tendsto 1 zero_lt_one).div_const (2*Real.pi)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  have ht := (tripleTestBase_bounds T hT).1
  simp only [Real.rpow_neg_one,tripleTestBase] 
  field_simp

theorem tripleBoundary_base_log_decay (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun T : ℝ => (tripleTestBase T)^(-a)*Real.log T^k) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tripleTest_envelope_tendsto a ha)
  · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
    have ht := (tripleTestBase_bounds T hT).1
    have hb := (tripleTestBase_bounds T hT).2.1
    have hq : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    positivity
  · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
    have ht := (tripleTestBase_bounds T hT).1
    have hq : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hl : Real.log T ≤ Real.log (2*T+2) := Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hq hl k).trans
      (pow_le_pow_right₀ (tripleBudget_height_log T ht) hk))
      (Real.rpow_nonneg (by linarith [(tripleTestBase_bounds T hT).2.1]) _)

theorem tripleBoundary_uniform_of_envelope {α : Type*} (F : ℝ → α → ℂ) (f : α → ℂ)
    (s : Set α) (E : ℝ → ℝ) (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop, ∀ p ∈ s, ‖F T p-f p‖ ≤ E T) :
    TendstoUniformlyOn F f atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : ∀ᶠ T in atTop, E T < ε := (tendsto_order.1 hE).2 ε hε
  filter_upwards [hbound,he] with T hb ht
  intro p hp
  rw [dist_comm,dist_eq_norm]
  exact (hb p hp).trans_lt ht

end
end HigherCorrelations
