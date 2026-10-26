import HigherCorrelations.TripleBudgetNamedInterior
import HigherCorrelations.TripleBudgetLimit

/-! UNCONDITIONAL uniform additive approximation to the exact full-zero master
observable. The retained expression is not replaced by an ordinate-only statistic.
All coefficient cutoffs were removed before this fixed-weight height limit. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem tripleBudget_uniform_lower_scale : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T R X Y : ℝ,
      0≤W → (∀ u, ω u≤W) → 3≤T → 1≤R → R≤X → R≤Y → X*Y≤T/R →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖ ≤
          C*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
  obtain ⟨K,hK,hrem⟩ := tripleBudget_remainder_words_uniform
  refine ⟨tripleBudgetNamedConstant+K,by linarith [tripleBudgetNamedConstant_pos],?_⟩
  intro ω hω W T R X Y hW hωW hT hR hXR hYR hZ
  have hx : 1≤X := hR.trans hXR
  have hy : 1≤Y := hR.trans hYR
  have he := tripleBudget_exact ω hω.smooth.continuous (tripleBudgetWeight_support ω hω) T X Y hT hx hy
  rw [he]
  have hs : tripleBudgetRetained ω T X Y + (∑ e, tripleBudgetError ω T X Y e) +
      (∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w) - tripleBudgetRetained ω T X Y =
      (∑ e, tripleBudgetError ω T X Y e)+(∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w) := by abel
  rw [hs]
  apply (norm_add_le _ _).trans
  have hn := tripleBudget_named_interior ω hω T R X Y hT hR hXR hYR hZ
  have hr := hrem ω hω W T R X Y hW hωW hT hR hXR hYR hZ
  have hL := tripleBudget_height_log T hT
  have hL24 : Real.log (2*T+2)^2≤Real.log (2*T+2)^4 := pow_le_pow_right₀ hL (by omega)
  have hD := fourierDerivativeL1_nonneg ω 1
  have ha : tripleBudgetNamedConstant*(1+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 ≤
      tripleBudgetNamedConstant*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
    have hc := tripleBudgetNamedConstant_pos.le
    gcongr
    linarith
  have hb : K*(1+W)/R*Real.log (2*T+2)^2 ≤ K*(1+W+fourierDerivativeL1 ω 1)/R*Real.log (2*T+2)^4 := by
    apply mul_le_mul _ hL24 (sq_nonneg _) (by positivity)
    apply div_le_div_of_nonneg_right _ (by linarith : 0≤R)
    exact mul_le_mul_of_nonneg_left (by linarith : 1+W≤1+W+fourierDerivativeL1 ω 1) hK.le
  convert add_le_add (hn.trans ha) (hr.trans hb) using 1 <;> ring

/-- The constant is chosen before the margin, weight, height, and prime scales. -/
theorem tripleBudget_uniform_asymptotic : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W ε T X Y : ℝ,
      0≤W → (∀ u, ω u≤W) → 0<ε → ε<1/3 → 3≤T →
      T^ε≤X → T^ε≤Y → X*Y≤T^(1-ε) →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖ ≤
          C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T := by
  obtain ⟨C,hC,hbound⟩ := tripleBudget_uniform_lower_scale
  refine ⟨C,hC,?_⟩
  intro ω hω W ε T X Y hW hωW hε _hεupper hT hX hY hZ
  have ht : 0<T := by linarith
  have hR : 1≤T^ε := Real.one_le_rpow (by linarith) hε.le
  have hz : X*Y≤T/T^ε := by simpa only [Real.rpow_sub ht,Real.rpow_one] using hZ
  have h := hbound ω hω W T (T^ε) X Y hW hωW hT hR hX hY hz
  convert h using 1
  rw [tripleBudgetEnvelope,Real.rpow_neg ht.le]
  ring

/-- Uniform additive o(1), stated with the moving parameter range explicitly.
The weight and strictly positive margin are fixed before T tends to infinity. -/
theorem tripleBudget_uniform_additive_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (W ε : ℝ) (hW : 0≤W) (hωW : ∀ u, ω u≤W) (hε : 0<ε) (hεupper : ε<1/3) :
    ∀ η : ℝ, 0<η → ∀ᶠ T : ℝ in atTop, ∀ X Y : ℝ,
      T^ε≤X → T^ε≤Y → X*Y≤T^(1-ε) →
        ‖tripleMasterObservable ω T X Y-tripleBudgetRetained ω T X Y‖<η := by
  obtain ⟨C,hC,hbound⟩ := tripleBudget_uniform_asymptotic
  have he := (tripleBudgetEnvelope_tendsto ε W (fourierDerivativeL1 ω 1) hε hW
    (fourierDerivativeL1_nonneg ω 1)).const_mul C
  simp only [mul_zero] at he
  intro η hη
  have he' : ∀ᶠ T : ℝ in atTop, C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T<η :=
    he.eventually (gt_mem_nhds hη)
  filter_upwards [eventually_ge_atTop (3:ℝ),he'] with T hT hsmall
  intro X Y hX hY hZ
  exact (hbound ω hω W ε T X Y hW hωW hε hεupper hT hX hY hZ).trans_lt hsmall

end
end HigherCorrelations
