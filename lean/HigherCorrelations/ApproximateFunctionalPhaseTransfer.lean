import HigherCorrelations.ApproximateFunctionalChiEstimate

/-! UNCONDITIONAL control of the error from replacing chi by its explicit
phase in both cutoff orders. No bound for the exact AFE remainder is assumed
or concluded here. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem afe_phase_replacement_identity (σ t x y : ℝ) :
    afePhaseRemainder σ t x y - afeRemainder (afePoint σ t) x y =
      (pairChi (afePoint σ t)-afePhase σ t)*afePolynomial (1-afePoint σ t) y := by
  rw [afe_phase_remainder_split]; ring

theorem afe_phase_replacement_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t x y : ℝ,
      1/2 ≤ σ → σ ≤ 1 → 2*Real.pi ≤ |t| → 1 ≤ x → x ≤ y →
      2*Real.pi*x*y = |t| →
      ‖afePhaseRemainder σ t x y-afeRemainder (afePoint σ t) x y‖ ≤ C*x^(-σ) ∧
      ‖afePhaseRemainder σ t y x-afeRemainder (afePoint σ t) y x‖ ≤
        C*afeHeight t^(1/2-σ)*x^(σ-1) := by
  obtain ⟨C,hC,hbound⟩ := afeChi_phase_uniform
  refine ⟨C,hC,fun σ t x y hσ hσ' ht hx hxy hprod => ?_⟩
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have htp : 0 < |t| := lt_of_lt_of_le (by positivity) ht
  have hπ : 1 ≤ 2*Real.pi := by have := Real.pi_gt_three; linarith
  have hχ := hbound σ t hσ hσ' ht
  have hq := afeHeight_ge_one ht
  have hw : 0 ≤ afeHeight t^(1/2-σ) := Real.rpow_nonneg (afeHeight_nonneg t) _
  have hw' : afeHeight t^(1/2-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith)
  have hPx := afePolynomial_norm_le (1-afePoint σ t) (by simp [afePoint]; linarith) hxpos.le
  have hPy := afePolynomial_norm_le (1-afePoint σ t) (by simp [afePoint]; linarith) hypos.le
  have hbx : ‖afePhaseRemainder σ t x y-afeRemainder (afePoint σ t) x y‖ ≤
      (C*afeHeight t^(1/2-σ)/|t|)*y := by
    rw [afe_phase_replacement_identity, norm_mul]
    exact mul_le_mul hχ hPy (norm_nonneg _) (by positivity)
  have hby : ‖afePhaseRemainder σ t y x-afeRemainder (afePoint σ t) y x‖ ≤
      (C*afeHeight t^(1/2-σ)/|t|)*x := by
    rw [afe_phase_replacement_identity, norm_mul]
    exact mul_le_mul hχ hPx (norm_nonneg _) (by positivity)
  have hyτ : y/|t| ≤ 1/x := by
    apply (div_le_div_iff₀ htp hxpos).mpr
    have := mul_le_mul_of_nonneg_right hπ (mul_nonneg hxpos.le hypos.le)
    nlinarith
  have hxτ : x/|t| ≤ 1/x := by
    apply (div_le_div_iff₀ htp hxpos).mpr
    have h₁ := mul_le_mul_of_nonneg_left hxy hxpos.le
    have h₂ := mul_le_mul_of_nonneg_right hπ (mul_nonneg hxpos.le hypos.le)
    nlinarith
  constructor
  · apply hbx.trans
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw' hC.le)
      (div_nonneg hypos.le htp.le)
    have h₂ := mul_le_mul_of_nonneg_left hyτ hC.le
    have hp : 1/x ≤ x^(-σ) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have h₃ := mul_le_mul_of_nonneg_left hp hC.le
    calc
      _ = (C*afeHeight t^(1/2-σ))*(y/|t|) := by ring
      _ ≤ C*(y/|t|) := by simpa using h₁
      _ ≤ C*(1/x) := h₂
      _ ≤ _ := h₃
  · apply hby.trans
    have hp : 1/x ≤ x^(σ-1) := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    calc
      _ = (C*afeHeight t^(1/2-σ))*(x/|t|) := by ring
      _ ≤ (C*afeHeight t^(1/2-σ))*(1/x) :=
        mul_le_mul_of_nonneg_left hxτ (mul_nonneg hC.le hw)
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hC.le hw)

end
end HigherCorrelations
