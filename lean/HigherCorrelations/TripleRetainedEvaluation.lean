import HigherCorrelations.TripleRetainedBounds

/-! UNCONDITIONAL consolidated retained-term evaluation. The bounds are
additive, with an existential diagonal constant and explicit other constants. -/
namespace HigherCorrelations
noncomputable section

theorem tripleRetained_evaluation : ∃ C : ℝ, 0 < C ∧ ∀ (ω : ℝ → ℝ) (T X Y : ℝ),
    TripleBudgetWeight ω → 3 ≤ T → 1 ≤ X → 1 ≤ Y →
    tripleBudgetRetained ω T X Y =
      (tripleRetainedMain ω T X Y+tripleRetainedErrorD ω T X Y+
        tripleRetainedErrorJ ω T X Y-triplePrimeResonantMass X Y : ℝ) ∧
    (0 ≤ tripleSmoothingMean ω ∧ tripleSmoothingMean ω ≤ Real.log 2) ∧
    0 ≤ tripleRetainedG X Y ∧
    |tripleRetainedErrorD ω T X Y| ≤ C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y ∧
    (0 ≤ tripleRetainedErrorJ ω T X Y ∧ tripleRetainedErrorJ ω T X Y ≤ 2*tripleRetainedG X Y/T) ∧
    (0 ≤ triplePrimeResonantMass X Y ∧ triplePrimeResonantMass X Y ≤
      tripleResonanceDecayConstant*tripleResonanceScale (X*Y)) ∧
    ‖tripleBudgetRetained ω T X Y-(tripleRetainedMain ω T X Y:ℂ)‖ ≤
      C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y+2*tripleRetainedG X Y/T+
      tripleResonanceDecayConstant*tripleResonanceScale (X*Y) := by
  obtain ⟨C,hC,hD⟩ := tripleRetainedErrorD_uniform
  refine ⟨C,hC,?_⟩
  intro ω T X Y hω hT hX hY
  exact ⟨tripleRetained_exact ω T X Y hX hY,tripleSmoothingMean_bounds ω hω,
    tripleRetainedG_nonneg X Y hX hY,hD ω T X Y hω hT hX hY,
    tripleRetainedErrorJ_bounds ω hω T X Y (by linarith) hX hY,
    triplePrimeResonantMass_decay X Y hX hY,
    tripleRetained_combined_bound C ω hω T X Y hT hX hY (hD ω T X Y hω hT hX hY)⟩

end
end HigherCorrelations
