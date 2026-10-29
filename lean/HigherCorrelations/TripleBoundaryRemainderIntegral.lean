import HigherCorrelations.TripleBoundaryRemainders
import HigherCorrelations.TripleBoundaryBox

/-! UNCONDITIONAL integration of all nineteen remainder words. This keeps the
axis boundary layers visible before height-logarithm comparisons are applied. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem tripleBoundary_remainder_integral : ∃ K : ℝ, 0<K ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T κ M : ℝ,
    0≤W → (∀ u, ω u≤W) → 2*Real.pi<T → 0<κ → 0≤M →
    ∀ (ψ : ℝ × ℝ → ℂ),
    (∀ p ∈ tripleQuadrant, ‖ψ p‖≤M) →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2≤1-κ) →
    (∫ p : ℝ × ℝ, ‖tripleQuadrantAmplitude ψ p‖*
      (∑ w ∈ tripleBudgetRemainderWords,
        ‖tripleBudgetWordError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) w‖)) ≤
    M*K*(1+W)*(2*Real.log (2*T+2)/Real.log (tripleTestBase T)+
      Real.log (2*T+2)^2/Real.log (tripleTestBase T)^2) := by
  obtain ⟨K,hK,hbound⟩ := tripleBoundary_remainder_bound
  refine ⟨K,hK,?_⟩
  intro ω hω W T κ M hW hωW hT hκ hM ψ hψ hs
  let b := Real.log (tripleTestBase T)
  let L := Real.log (2*T+2)
  let E : ℝ × ℝ → ℝ := fun p => L*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
    L^2*(Real.exp (-(b*p.1))*Real.exp (-(b*p.2)))
  have hbase := tripleTestBase_bounds T hT
  have hb : 0<b := Real.log_pos hbase.2.1
  have hL : 0≤L := (tripleBudget_height_log T hbase.1).trans' (by norm_num)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hi : Integrable (tripleBoundaryBox.indicator (fun p => M*K*(1+W)*E p)) :=
    (hE.const_mul _).continuousOn.integrableOn_compact tripleBoundaryBox_compact
      |>.integrable_indicator tripleBoundaryBox_measurable
  have hpoint (p : ℝ × ℝ) :
      ‖tripleQuadrantAmplitude ψ p‖*(∑ w ∈ tripleBudgetRemainderWords,
        ‖tripleBudgetWordError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) w‖) ≤
      tripleBoundaryBox.indicator (fun p => M*K*(1+W)*E p) p := by
    by_cases hz : tripleQuadrantAmplitude ψ p=0
    · rw [hz,norm_zero,zero_mul]
      by_cases hp : p ∈ tripleBoundaryBox
      · rw [indicator_of_mem hp]
        dsimp [E]
        positivity
      · rw [indicator_of_notMem hp]
    have hp := tripleQuadrantAmplitude_support ψ κ hs hz
    have hbox := tripleQuadrantMargin_subset_box κ hκ.le hp
    have hq : p ∈ tripleQuadrant := ⟨hp.1,hp.2.1⟩
    have hnorm : ‖tripleQuadrantAmplitude ψ p‖≤M := by simpa [tripleQuadrantAmplitude,hq] using hψ p hq
    obtain ⟨hx,hy,hzbase⟩ := tripleQuadrant_scale_range κ T p hT hp
    have hzt : (tripleTestBase T)^p.1*(tripleTestBase T)^p.2≤T := by
      apply hzbase.trans
      apply le_trans (Real.rpow_le_rpow_of_exponent_le hbase.2.1.le (show 1-κ≤(1:ℝ) by linarith))
      simpa using hbase.2.2
    have hh := hbound ω hω W T _ _ hW hωW hbase.1 hx hy hzt
    have he : Real.log (2*T+2)*(1/(tripleTestBase T)^p.1+1/(tripleTestBase T)^p.2)+
        Real.log (2*T+2)^2/((tripleTestBase T)^p.1*(tripleTestBase T)^p.2) = E p := by
      simp only [Real.rpow_def_of_pos (show 0<tripleTestBase T by linarith [hbase.2.1]),
        div_eq_mul_inv,mul_inv,one_mul,← Real.exp_neg,E,b,L]
    rw [he] at hh
    rw [indicator_of_mem hbox]
    have hn : 0≤∑ w ∈ tripleBudgetRemainderWords,
        ‖tripleBudgetWordError ω T ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2) w‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hpos : 0≤K*(1+W)*E p := by dsimp [E]; positivity
    have hm := mul_le_mul hnorm hh hn hM
    convert hm using 1 <;> ring
  have hh := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun p => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))) hi
    (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator tripleBoundaryBox_measurable,integral_const_mul] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (tripleBoundary_box_envelope L b hL hb) (by positivity)

end
end HigherCorrelations
