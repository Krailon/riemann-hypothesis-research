import HigherCorrelations.TripleQuadrantResidual
import HigherCorrelations.TripleTestAsymptotic

/-! UNCONDITIONAL quadrant asymptotic, for a fixed positive upper support margin.
All zero-occurrence cutoffs are removed at fixed height before this limit. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem tripleQuadrant_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0 ≤ W → (∀ u, ω u ≤ W) →
    ∀ (ψ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1 ≤ T → 0 < κ →
    (∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) →
    ‖tripleQuadrantStatistic ω ψ T-tripleQuadrantLimit ψ‖ ≤
      C*tripleQuadrantN1 ψ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by
  obtain ⟨A,hA,ha⟩ := tripleQuadrant_main_bound
  obtain ⟨D,hD,hd⟩ := tripleQuadrant_residual_bound
  refine ⟨A+D,by positivity,?_⟩
  intro ω hω W hW hw ψ hψ hc T κ hT hκ hs
  have hm := ha ω hω ψ hψ hc T κ hT hκ.le hs
  have he := hd ω hω W hW hw ψ hψ hc T κ hT hκ hs
  let S := tripleQuadrantN1 ψ
  let V := 1+W+fourierDerivativeL1 ω 1
  let E := 1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3
  have hS : 0 ≤ S := (tripleQuadrantN1_bounds ψ hψ hc).1
  have ht := tripleBoundary_height T hT
  have hb : 0 < Real.log (tripleTestBase T) := by linarith [ht.2.1]
  have hV : 1 ≤ V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hE : 1/Real.log (tripleTestBase T) ≤ E := by
    dsimp [E]
    have hP := Real.rpow_nonneg (show 0 ≤ tripleTestBase T by
      linarith [(tripleTestBase_bounds T ht.1).2.1]) (-κ)
    have hL := tripleBudget_height_log T (tripleTestBase_bounds T ht.1).1
    exact le_add_of_nonneg_right (mul_nonneg hP (pow_nonneg (by linarith) 3))
  have hm' : A*S/Real.log (tripleTestBase T) ≤ A*S*V*E := by
    calc
      _ = A*S*(1/Real.log (tripleTestBase T)) := by ring
      _ ≤ A*S*E := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hV (show 0 ≤ A*S*E by
          have : 0 ≤ E := (by positivity : 0 ≤ 1/Real.log (tripleTestBase T)).trans hE
          positivity)
        nlinarith only [hh]
  have hh := dist_triangle (tripleQuadrantStatistic ω ψ T)
    ((∫ p in tripleQuadrant, ψ p*(tripleRetainedMain ω T
      ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2):ℂ))/(Real.log T:ℂ)) (tripleQuadrantLimit ψ)
  simp only [dist_eq_norm] at hh
  exact hh.trans ((add_le_add he (hm.trans hm')).trans_eq (by dsimp [S,V,E]; ring))

theorem tripleQuadrant_envelope_tendsto (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun T : ℝ => 1/Real.log (tripleTestBase T)+
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) atTop (𝓝 0) := by
  have hB : Tendsto tripleTestBase atTop atTop := by
    exact tendsto_id.atTop_div_const (by positivity : 0 < 2*Real.pi)
  have hlog := Real.tendsto_log_atTop.comp hB
  have hfirst : Tendsto (fun T => 1/Real.log (tripleTestBase T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hsecond : Tendsto (fun T => (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (tripleTest_envelope_tendsto κ hκ)
    · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
      have hB := (tripleTestBase_bounds T hT).2.1
      have hL := tripleBudget_height_log T (tripleTestBase_bounds T hT).1
      positivity
    · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (tripleBudget_height_log T (tripleTestBase_bounds T hT).1) (by omega))
        (Real.rpow_nonneg (by linarith [(tripleTestBase_bounds T hT).2.1]) _)
  simpa only [add_zero] using hfirst.add hsecond

theorem tripleQuadrant_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (κ : ℝ) (hκ : 0 < κ)
    (hs : ∀ p ∈ tripleQuadrant, ψ p ≠ 0 → p.1+p.2 ≤ 1-κ) :
    Tendsto (fun T => tripleQuadrantStatistic ω ψ T) atTop (𝓝 (tripleQuadrantLimit ψ)) := by
  have hcω : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  obtain ⟨W,hw⟩ := hcω.exists_bound_of_continuous hω.smooth.continuous
  have hW : 0 ≤ W := (norm_nonneg (ω 0)).trans (hw 0)
  have hw' : ∀ u, ω u ≤ W := fun u => (le_abs_self _).trans (by simpa using hw u)
  obtain ⟨C,hC,h⟩ := tripleQuadrant_uniform_bound
  have he := (tripleQuadrant_envelope_tendsto κ hκ).const_mul
    (C*tripleQuadrantN1 ψ*(1+W+fourierDerivativeL1 ω 1))
  simp only [mul_zero] at he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _)) _ he
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp 1)] with T hT
  exact h ω hω W hW hw' ψ hψ hc T κ hT hκ hs

end
end HigherCorrelations
