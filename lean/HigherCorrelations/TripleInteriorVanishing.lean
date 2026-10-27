import HigherCorrelations.TripleInteriorBounds
import HigherCorrelations.TripleMasterAssembly

/-! UNCONDITIONAL uniform interior vanishing. All series were defined at fixed
parameters in the imported identities. Fix a positive margin and smoothing
before taking the height limit; the prime scales may vary throughout the stated
closed range. This is the native full-zero observable, with no ordinate-only
replacement or extension to the frequency axes. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem tripleInterior_cubic_envelope_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun T : ℝ => T^(-ε)*Real.log (2*T+2)^3) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tripleBudgetEnvelope_tendsto ε 0 0 hε le_rfl le_rfl)
  · filter_upwards [eventually_ge_atTop (3:ℝ)] with T hT
    have hL := tripleBudget_height_log T hT
    positivity
  · filter_upwards [eventually_ge_atTop (3:ℝ)] with T hT
    have hL := tripleBudget_height_log T hT
    have hp : Real.log (2*T+2)^3 ≤ Real.log (2*T+2)^4 := pow_le_pow_right₀ hL (by omega)
    simpa [tripleBudgetEnvelope] using mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by linarith : 0 ≤ T) (-ε))

theorem tripleInterior_retained_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ε : ℝ) (hε : 0 < ε) (hεupper : ε < 1/3) :
    ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop, ∀ X Y : ℝ,
    T^ε ≤ X → T^ε ≤ Y → X*Y ≤ T^(1-ε) → ‖tripleBudgetRetained ω T X Y‖ < η := by
  obtain ⟨C,hC,hbound⟩ := tripleInterior_retained_bound
  have he := (tripleInterior_cubic_envelope_tendsto ε hε).const_mul C
  simp only [mul_zero] at he
  intro η hη
  have he' : ∀ᶠ T : ℝ in atTop, C*(T^(-ε)*Real.log (2*T+2)^3) < η :=
    he.eventually (gt_mem_nhds hη)
  filter_upwards [eventually_ge_atTop (3:ℝ),he'] with T hT hsmall
  intro X Y hX hY hZ
  exact (hbound ω hω ε T X Y hε hεupper hT hX hY hZ).trans_lt (by simpa [mul_assoc] using hsmall)

theorem tripleInterior_observable_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (W ε : ℝ) (hW : 0 ≤ W) (hωW : ∀ u, ω u ≤ W) (hε : 0 < ε) (hεupper : ε < 1/3) :
    ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop, ∀ X Y : ℝ,
    T^ε ≤ X → T^ε ≤ Y → X*Y ≤ T^(1-ε) → ‖tripleMasterObservable ω T X Y‖ < η := by
  obtain ⟨C,hC,hbound⟩ := tripleInterior_observable_bound
  have he := (tripleBudgetEnvelope_tendsto ε W (fourierDerivativeL1 ω 1) hε hW
    (fourierDerivativeL1_nonneg ω 1)).const_mul C
  simp only [mul_zero] at he
  intro η hη
  have he' : ∀ᶠ T : ℝ in atTop, C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) T < η :=
    he.eventually (gt_mem_nhds hη)
  filter_upwards [eventually_ge_atTop (3:ℝ),he'] with T hT hsmall
  intro X Y hX hY hZ
  exact (hbound ω hω W ε T X Y hW hωW hε hεupper hT hX hY hZ).trans_lt hsmall

/-- Compact support supplies the weight bound, so every admissible fixed weight
has the uniform vanishing property without an additional boundedness premise. -/
theorem tripleInterior_fixed_weight_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (ε : ℝ) (hε : 0 < ε) (hεupper : ε < 1/3) :
    ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop, ∀ X Y : ℝ,
    T^ε ≤ X → T^ε ≤ Y → X*Y ≤ T^(1-ε) → ‖tripleMasterObservable ω T X Y‖ < η := by
  have hc : HasCompactSupport ω := HasCompactSupport.of_support_subset_isCompact
    isCompact_Icc (tripleBudgetWeight_support ω hω)
  obtain ⟨W,hW⟩ := hc.exists_bound_of_continuous hω.smooth.continuous
  have hW0 : 0 ≤ W := (norm_nonneg (ω 0)).trans (hW 0)
  have hw : ∀ u, ω u ≤ W := fun u => (le_abs_self (ω u)).trans (by simpa [Real.norm_eq_abs] using hW u)
  exact tripleInterior_observable_limit ω hω W ε hW0 hw hε hεupper

/-- The lower corner and both upper corners lie in the closed moving range. -/
theorem tripleInterior_power_endpoints (ε T : ℝ) (hε : 0 < ε) (hεupper : ε < 1/3)
    (hT : 3 ≤ T) :
    T^ε*T^ε ≤ T^(1-ε) ∧ T^ε ≤ T^(1-2*ε) ∧
    T^ε*T^(1-2*ε) = T^(1-ε) ∧ T^(1-2*ε)*T^ε = T^(1-ε) := by
  have ht : 0 < T := by linarith
  have h1 : 1 ≤ T := by linarith
  have he : ε ≤ 1-2*ε := by linarith
  have hab : T^ε*T^(1-2*ε) = T^(1-ε) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  refine ⟨?_,Real.rpow_le_rpow_of_exponent_le h1 he,hab,?_⟩
  · rw [← Real.rpow_add ht]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · rw [mul_comm]
    exact hab

/-- Exchange symmetry is inherited with the full zero coordinates retained. -/
theorem tripleInterior_exchange (ω : ℝ → ℝ) (T R X Y : ℝ) (hR : 1 ≤ R)
    (hX : R ≤ X) (hY : R ≤ Y) :
    tripleBudgetRetained ω T Y X = tripleBudgetRetained ω T X Y ∧
    tripleMasterObservable ω T Y X = tripleMasterObservable ω T X Y := by
  exact ⟨tripleBudgetRetained_swap ω T Y X (hR.trans hY) (hR.trans hX),
    tripleMasterObservable_swap ω T Y X⟩

/-- The minimal height is included; only the margin endpoints are excluded. -/
theorem tripleInterior_height_three : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W ε X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 0 < ε → ε < 1/3 →
    (3:ℝ)^ε ≤ X → (3:ℝ)^ε ≤ Y → X*Y ≤ (3:ℝ)^(1-ε) →
    ‖tripleMasterObservable ω 3 X Y‖ ≤ C*tripleBudgetEnvelope ε W (fourierDerivativeL1 ω 1) 3 := by
  obtain ⟨C,hC,h⟩ := tripleInterior_observable_bound
  exact ⟨C,hC,fun ω hω W ε X Y hW hωW hε hεupper hX hY hZ =>
    h ω hω W ε 3 X Y hW hωW hε hεupper le_rfl hX hY hZ⟩

end
end HigherCorrelations
