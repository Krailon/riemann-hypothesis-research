import HigherCorrelations.TripleBoundaryNamed
import HigherCorrelations.TripleBoundaryRemainders
import HigherCorrelations.TripleBoundaryRetained

/-! UNCONDITIONAL pointwise error envelope before integration. Named prime,
remainder, diagonal, smoothing and resonance losses are still separate. -/
namespace HigherCorrelations
noncomputable section

set_option maxHeartbeats 800000 in
theorem tripleBoundary_pointwise : ∃ A : ℝ, 0<A ∧ ∃ H : ℝ, 0<H ∧ ∃ D : ℝ, 0<D ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0≤W → (∀ u, ω u≤W) → 3≤T → 1≤X → 1≤Y → X*Y≤T →
    ‖tripleQuadrantRemainder ω T X Y‖ ≤
    A*(1+fourierDerivativeL1 ω 1)*(Real.log (2*T+2)^2/(X*Y)^2+
      Real.log (2*T+2)^3/T+(X*Y)/T*Real.log (2*T+2)^4) +
    H*(1+W)*(Real.log (2*T+2)*(1/X+1/Y)+Real.log (2*T+2)^2/(X*Y)) +
    D*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y+
    2*tripleRetainedG X Y/T+tripleResonanceDecayConstant*tripleResonanceScale (X*Y) := by
  obtain ⟨A,hA,ha⟩ := tripleBoundary_named_bound
  obtain ⟨H,hH,hh⟩ := tripleBoundary_remainder_bound
  obtain ⟨D,hD,hd⟩ := tripleRetainedErrorD_uniform
  refine ⟨A,hA,H,hH,D,hD,?_⟩
  intro ω hω W T X Y hW hωW hT hX hY hZT
  have hn := ha ω hω T X Y hT hX hY hZT
  have hr := hh ω hω W T X Y hW hωW hT hX hY hZT
  have he := tripleRetained_combined_bound D ω hω T X Y hT hX hY
    (hd ω T X Y hω hT hX hY)
  have hidentity : tripleQuadrantRemainder ω T X Y =
      ((∑ e : TripleBudgetError, tripleBudgetError ω T X Y e)+
        ∑ w ∈ tripleBudgetRemainderWords, tripleBudgetWordError ω T X Y w) +
      (tripleBudgetRetained ω T X Y-(tripleRetainedMain ω T X Y:ℂ)) := by
    rw [tripleQuadrantRemainder,tripleBudget_exact ω hω.smooth.continuous
      (tripleBudgetWeight_support ω hω) T X Y hT hX hY]
    ring
  rw [hidentity]
  have hfirst := (norm_add_le _ _).trans
    (add_le_add ((norm_sum_le _ _).trans hn) ((norm_sum_le _ _).trans hr))
  have hfull := (norm_add_le _ _).trans (add_le_add hfirst he)
  convert hfull using 1 <;> ring

end
end HigherCorrelations
