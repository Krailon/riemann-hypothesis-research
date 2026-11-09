import HigherCorrelations.ReplacementAmplitudeDecay
import HigherCorrelations.ConstantReplacementScaling

/-! UNCONDITIONAL specialization of the uniform Fourier bound to actual zero tuples. -/
namespace HigherCorrelations
noncomputable section
open scoped ContDiff

theorem replacementHeight_bounds (T : ℝ) (hT : 2*Real.pi*Real.exp 1 ≤ T) :
    0 < T ∧ 0 < Real.log T ∧ 0 < meanSpacing T ∧
    0 ≤ Real.log (T/(2*Real.pi)) ∧ Real.log (T/(2*Real.pi)) ≤ Real.log T := by
  have he : 1 < Real.exp (1:ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have htp : 2*Real.pi<T := by nlinarith [Real.pi_pos]
  have ht : 1 < T := by nlinarith [Real.pi_gt_three]
  have hb : 0 < Real.log (T/(2*Real.pi)) := Real.log_pos ((one_lt_div (by positivity)).mpr htp)
  refine ⟨by linarith, Real.log_pos ht, meanSpacing_pos T htp, hb.le, ?_⟩
  apply Real.log_le_log (by positivity)
  apply div_le_self (by linarith)
  linarith [Real.pi_gt_three]

theorem replacementTuple_bound (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (s T : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hT : 2*Real.pi*Real.exp 1 ≤ T)
    (hsupp : ∀ p ∈ tsupport φ, signedGauge p ≤ s) (v : ReplacementTriple) :
    ‖replacementTuple φ T v‖ ≤ replacementDecayConstant*replacementP24 φ*
      (replacementHorizontal T v)^2*(1+replacementHorizontal T v)^22*
      Real.exp (2*s*replacementHorizontal T v)/(1+replacementRadius T v)^22 := by
  have ht := replacementHeight_bounds T hT
  have hx := replacementHorizontal_bounds T ht.2.1.le v
  let θ := fun j => Real.log (T/(2*Real.pi))*replacementDelta v j
  have hθ (j) : |θ j| ≤ replacementHorizontal T v := by
    dsimp [θ]
    rw [abs_mul, abs_of_nonneg ht.2.2.2.1]
    exact (mul_le_mul_of_nonneg_right ht.2.2.2.2 (abs_nonneg _)).trans (hx.2.2 j)
  have he : replacementCosh (Real.log (T/(2*Real.pi))) (replacementDelta v) = replacementCosh 1 θ := by
    funext p
    unfold replacementCosh θ
    push_cast
    ring_nf
  unfold replacementTuple
  rw [he]
  exact replacementCosh_fourier_bound φ hφ hc θ _ s hx.1 hs1.le hθ hsupp (actualGaps (meanSpacing T) v)

end
end HigherCorrelations
