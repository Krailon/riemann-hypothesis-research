import HigherCorrelations.ProfileTransferIdentity
import HigherCorrelations.TripleBoundaryHeight

/-! UNCONDITIONAL normalized transfer estimates. The raw smoothing losses
are retained before the height comparison simplifies them. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem frozenTransferError_raw_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
    tsupport φ ⊆ signedMargin κ →
    ‖frozenTransferError ω φ T‖ ≤
      8*C*tripleTestL1 φ*(tripleTestBase T)^(1-κ)/(T*Real.log T)*
        ((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3) := by
  obtain ⟨C,hC,h⟩ := tripleLocalizationError_weighted_bound
  refine ⟨C,hC,fun ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs => ?_⟩
  obtain ⟨he,hb⟩ := h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs
  have hq : 0<Real.log T := Real.log_pos (by linarith [Real.pi_gt_three])
  have hn : ‖(8/(Real.log T:ℂ))‖=8/Real.log T := by
    rw [norm_div,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq]
  rw [frozenTransferError,norm_mul,hn]
  have hh := mul_le_mul_of_nonneg_left ((norm_tsum_le_tsum_norm he).trans hb)
    (show 0≤8/Real.log T by positivity)
  exact hh.trans_eq (by ring)

theorem profileTransfer_power_scale (κ T : ℝ) (hT : 2*Real.pi<T) :
    (tripleTestBase T)^(1-κ)/T=(tripleTestBase T)^(-κ)/(2*Real.pi) := by
  have ht : 0<T := by linarith [(tripleTestBase_bounds T hT).1]
  have hb : 0<tripleTestBase T := by linarith [(tripleTestBase_bounds T hT).2.1]
  rw [show 1-κ=1+(-κ) by ring,Real.rpow_add hb,Real.rpow_one,tripleTestBase]
  field_simp

theorem profileTransfer_height_bounds (T : ℝ) (hT : 2*Real.pi*Real.exp 1≤T) :
    1≤Real.log T ∧ Real.log (2*T+2)≤tripleBoundaryLogConstant*Real.log T := by
  obtain ⟨ht,hb,hq,hL⟩ := tripleBoundary_height T hT
  have hp : 0≤Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨by linarith,?_⟩
  exact hL.trans (mul_le_mul_of_nonneg_left (by linarith) tripleBoundaryLogConstant_pos.le)

theorem profileTransfer_log_budget (M₀ M₁ T : ℝ) (hM₀ : 0≤M₀) (hM₁ : 0≤M₁)
    (hT : 2*Real.pi*Real.exp 1≤T) :
    (M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/Real.log T ≤
      (tripleBoundaryLogConstant+1)*(M₀+M₁)*Real.log (2*T+2)^3 := by
  obtain ⟨hq,hL⟩ := profileTransfer_height_bounds T hT
  have hl := tripleBudget_height_log T (tripleTestBase_bounds T (tripleBoundary_height T hT).1).1
  have hK := tripleBoundaryLogConstant_pos
  apply (div_le_iff₀ (by linarith : 0<Real.log T)).mpr
  have hh : M₁*Real.log (2*T+2)+M₀ ≤ (M₁*tripleBoundaryLogConstant+M₀)*Real.log T := by
    nlinarith [mul_le_mul_of_nonneg_left hL hM₁,le_mul_of_one_le_right hM₀ hq]
  have hc : M₁*tripleBoundaryLogConstant+M₀ ≤ (tripleBoundaryLogConstant+1)*(M₀+M₁) := by
    nlinarith [mul_nonneg hK.le hM₀]
  have h := mul_le_mul_of_nonneg_right
    (hh.trans (mul_le_mul_of_nonneg_right hc (by linarith)))
    (show 0≤Real.log (2*T+2)^3 by positivity)
  convert h using 1 <;> ring

theorem frozenTransferError_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖frozenTransferError ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+(M₁:ℝ))*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,h⟩ := frozenTransferError_raw_bound
  refine ⟨(8*C/(2*Real.pi))*(tripleBoundaryLogConstant+1),by
    have hK := tripleBoundaryLogConstant_pos
    positivity,fun ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs => ?_⟩
  have ht := (tripleBoundary_height T hT).1
  have hb : 0<tripleTestBase T := by linarith [(tripleTestBase_bounds T ht).2.1]
  have hφ0 : 0≤tripleTestL1 φ := integral_nonneg (fun _ => norm_nonneg _)
  apply (h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T ht hφs).trans
  calc
    _ = (8*C)*tripleTestL1 φ*((tripleTestBase T)^(1-κ)/T)*
        (((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/Real.log T) := by ring
    _ = ((8*C/(2*Real.pi))*tripleTestL1 φ*(tripleTestBase T)^(-κ))*
        (((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/Real.log T) := by
      rw [profileTransfer_power_scale κ T ht]
      ring
    _ ≤ ((8*C/(2*Real.pi))*tripleTestL1 φ*(tripleTestBase T)^(-κ))*
        ((tripleBoundaryLogConstant+1)*(M₀+(M₁:ℝ))*Real.log (2*T+2)^3) :=
      mul_le_mul_of_nonneg_left (profileTransfer_log_budget M₀ M₁ T hM₀ M₁.coe_nonneg hT) (by positivity)
    _ = _ := by ring

theorem frozenStatistic_transfer_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-frozenStatistic ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+(M₁:ℝ))*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,h⟩ := frozenTransferError_bound
  refine ⟨C,hC,fun ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs => ?_⟩
  rw [frozenStatistic_transfer_identity ω M₀ M₁ hM₀ hw hω hs φ hφ κ T (tripleBoundary_height T hT).1 hφs]
  exact h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs

theorem frozenStatistic_transfer_bound_deriv : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) →
    Differentiable ℝ ω → (∀ u, |deriv ω u|≤M₁) → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-frozenStatistic ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+M₁)*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,h⟩ := frozenStatistic_transfer_bound
  refine ⟨C,hC,fun ω M₀ M₁ hM₀ hM₁ hw hω hd hs φ hφ κ T hT hφs => ?_⟩
  apply h ω M₀ ⟨M₁,hM₁⟩ hM₀ hw _ hs φ hφ κ T hT hφs
  exact lipschitzWith_of_nnnorm_deriv_le hω (fun u => by
    change ‖deriv ω u‖≤M₁
    simpa only [Real.norm_eq_abs] using hd u)

end
end HigherCorrelations
