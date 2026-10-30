import HigherCorrelations.SignedTrace
import HigherCorrelations.SignedSeminorm
import HigherCorrelations.TripleQuadrantAsymptotic

/-! UNCONDITIONAL signed smoothed three-level passage. The support is strictly
inside the hexagon; full complex test arguments and the horizontal kernel remain.
All inherited analytic constants are existential, independent of the test and height. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem signed_uniform_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W : ℝ, 0≤W → (∀ u, ω u≤W) →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ T κ : ℝ, 2*Real.pi*Real.exp 1≤T → 0<κ → tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-signedLimit φ‖ ≤
      C*signedC1 φ*(1+W+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) := by
  obtain ⟨C,hC,h⟩ := tripleQuadrant_uniform_bound
  refine ⟨12*C,by positivity,?_⟩
  intro ω hω W hW hw φ hφ hc T κ hT hκ hs
  have ht := tripleBoundary_height T hT
  let V := 1+W+fourierDerivativeL1 ω 1
  let E := 1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3
  have hV : 0≤V := by dsimp [V]; linarith [fourierDerivativeL1_nonneg ω 1]
  have hE : 0≤E := by
    have hb : 0<Real.log (tripleTestBase T) := by linarith [ht.2.1]
    have hB := (tripleTestBase_bounds T ht.1).2.1
    have hL := tripleBudget_height_log T (tripleTestBase_bounds T ht.1).1
    dsimp [E]
    positivity
  have he (j : Fin 6) :
      ‖signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T)-
        signedConjugate j (tripleQuadrantLimit (signedPullback φ j))‖ ≤ C*(2*signedC1 φ)*V*E := by
    have hh := h ω hω W hW hw _ (signedPullback_smooth φ hφ j)
      (signedPullback_compact φ hc j) T κ hT hκ (signedPullback_support φ κ hs j)
    have hn : ‖signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T)-
        signedConjugate j (tripleQuadrantLimit (signedPullback φ j))‖ =
      ‖tripleQuadrantStatistic ω (signedPullback φ j) T-tripleQuadrantLimit (signedPullback φ j)‖ := by
      unfold signedConjugate
      split_ifs
      · rfl
      · rw [← star_sub,norm_star]
    rw [hn]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (signedPullback_N1_bound φ hφ hc j) hC.le) hV) hE)
  rw [signed_sector_decomposition ω hω φ hφ hc κ T hκ ht.1 hs,
    ← signed_limit_sector_sum φ hφ.continuous hc,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 6, ‖signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T)-
        signedConjugate j (tripleQuadrantLimit (signedPullback φ j))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 6, C*(2*signedC1 φ)*V*E := Finset.sum_le_sum (fun j _ => he j)
    _ = _ := by simp [V,E]; ring

theorem signed_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 (signedLimit φ)) := by
  have hj (j : Fin 6) : Tendsto (fun T => signedConjugate j (tripleQuadrantStatistic ω (signedPullback φ j) T))
      atTop (𝓝 (signedConjugate j (tripleQuadrantLimit (signedPullback φ j)))) := by
    have hh := tripleQuadrant_fixed_margin_limit ω hω _ (signedPullback_smooth φ hφ j)
      (signedPullback_compact φ hc j) κ hκ (signedPullback_support φ κ hs j)
    unfold signedConjugate
    split_ifs
    · exact hh
    · exact continuous_star.continuousAt.tendsto.comp hh
  have hh := tendsto_finset_sum Finset.univ (fun j _ => hj j)
  rw [signed_limit_sector_sum φ hφ.continuous hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  exact (signed_sector_decomposition ω hω φ hφ hc κ T hκ hT hs).symm

theorem signed_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (fun T => signedStatistic ω φ T) atTop (𝓝 (signedLimit φ)) := by
  obtain ⟨κ,hκ,hκ1,hmargin⟩ := signed_compact_margin φ hc hs
  exact signed_fixed_margin_limit ω hω φ hφ hc κ hκ hmargin

end
end HigherCorrelations
