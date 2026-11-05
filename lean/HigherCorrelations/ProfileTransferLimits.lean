import HigherCorrelations.ProfileTransferBounds
import HigherCorrelations.SignedAsymptotic
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! UNCONDITIONAL fixed-test profile limit. The inherited signed error and the
new localization-transfer error remain separate in the uniform bound.
No closed support-boundary or varying-margin limit is asserted. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem profileTransfer_envelope_tendsto (κ : ℝ) (hκ : 0<κ) :
    Tendsto (fun T : ℝ => (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tripleTest_envelope_tendsto κ hκ)
  · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
    have hb := (tripleTestBase_bounds T hT).2.1
    have hl := tripleBudget_height_log T (tripleTestBase_bounds T hT).1
    positivity
  · filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (tripleBudget_height_log T (tripleTestBase_bounds T hT).1) (by omega))
      (Real.rpow_nonneg (by linarith [(tripleTestBase_bounds T hT).2.1]) _)

theorem frozenTransferError_tendsto (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenTransferError ω φ) atTop (𝓝 0) := by
  obtain ⟨C,hC,h⟩ := frozenTransferError_bound
  have he := (profileTransfer_envelope_tendsto κ hκ).const_mul (C*tripleTestL1 φ*(M₀+(M₁:ℝ)))
  simp only [mul_zero] at he
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ he
  filter_upwards [eventually_ge_atTop (2*Real.pi*Real.exp 1)] with T hT
  simpa only [mul_assoc] using h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs

theorem frozenStatistic_transfer_tendsto (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T-frozenStatistic ω φ T) atTop (𝓝 0) := by
  apply (frozenTransferError_tendsto ω M₀ M₁ hM₀ hw hω hs φ hφ κ hκ hφs).congr'
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  exact (frozenStatistic_transfer_identity ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs).symm

theorem profileTransfer_smoothing_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    ∃ (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ ∧ (∀ u, |ω u|≤M₀) ∧ LipschitzWith M₁ ω := by
  have hc : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (tripleBudgetWeight_support ω hω)
  obtain ⟨M₀,hM₀⟩ := hc.exists_bound_of_continuous hω.smooth.continuous
  obtain ⟨M₁,hM₁⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hω.smooth (by simp)
  refine ⟨M₀,M₁,?_,?_,hM₁⟩
  · exact (norm_nonneg (ω 0)).trans (hM₀ 0)
  · simpa only [Real.norm_eq_abs] using hM₀

theorem frozenStatistic_uniform_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ (M₀ : ℝ) (M₁ : ℝ≥0),
    0≤M₀ → (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-signedLimit φ‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+(M₁:ℝ))*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨A,hA,ha⟩ := signed_uniform_bound
  obtain ⟨C,hC,hc⟩ := frozenStatistic_transfer_bound
  refine ⟨A,C,hA,hC,fun ω hω M₀ M₁ hM₀ hw hl φ hφ hφc κ T hκ hT hs => ?_⟩
  have hi := hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hφc
  have hmain := ha ω hω M₀ hM₀ (fun u => (le_abs_self _).trans (hw u)) φ hφ hφc T κ hT hκ hs
  have htransfer := hc ω M₀ M₁ hM₀ hw hl (tripleBudgetWeight_support ω hω) φ hi κ T hT hs
  calc
    _ = ‖(signedStatistic ω φ T-signedLimit φ)-(signedStatistic ω φ T-frozenStatistic ω φ T)‖ := by
      congr 1
      ring
    _ ≤ ‖signedStatistic ω φ T-signedLimit φ‖+‖signedStatistic ω φ T-frozenStatistic ω φ T‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add hmain htransfer

theorem frozenStatistic_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 (signedLimit φ)) := by
  obtain ⟨M₀,M₁,hM₀,hw,hl⟩ := profileTransfer_smoothing_bounds ω hω
  have hi := hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hc
  have he := frozenTransferError_tendsto ω M₀ M₁ hM₀ hw hl (tripleBudgetWeight_support ω hω) φ hi κ hκ hs
  have hh := (signed_fixed_margin_limit ω hω φ hφ hc κ hκ hs).sub he
  simp only [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (2*Real.pi)] with T hT
  have hid := frozenStatistic_transfer_identity ω M₀ M₁ hM₀ hw hl
    (tripleBudgetWeight_support ω hω) φ hi κ T hT hs
  linear_combination hid

theorem frozenStatistic_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 (signedLimit φ)) := by
  obtain ⟨κ,hκ,hκ1,hmargin⟩ := signed_compact_margin φ hc hs
  exact frozenStatistic_fixed_margin_limit ω hω φ hφ hc κ hκ hmargin

end
end HigherCorrelations
