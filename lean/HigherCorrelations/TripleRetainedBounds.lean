import HigherCorrelations.TripleRetainedAlgebra

/-! UNCONDITIONAL named errors with their parameter dependence preserved.
The sole existential constant comes from the checked mixed diagonal. -/
namespace HigherCorrelations
noncomputable section

theorem tripleRetainedDelta_uniform : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → a ≤ b → |tripleRetainedDelta a b| ≤ C*(a/b)*(1+Real.log (b/a)) := by
  obtain ⟨C,hC,h⟩ := tripleMixedDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  intro a b ha hab
  rw [tripleRetainedDelta_ordered a b hab]
  exact h a b ha hab

theorem tripleRetained_delta_term_bound (C X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hD : ∀ a b : ℝ, 1 ≤ a → a ≤ b → |tripleRetainedDelta a b| ≤ C*(a/b)*(1+Real.log (b/a))) :
    |tripleRetainedDelta X (X*Y)/Y| ≤ C*((1+Real.log Y)/Y^2) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hx : X*Y/X=Y := by field_simp
  have h := div_le_div_of_nonneg_right (hD X (X*Y) hX (by nlinarith)) hY0.le
  rw [hx] at h
  rw [abs_div,abs_of_pos hY0]
  convert h using 1
  field_simp
  <;> ring

theorem tripleRetainedErrorD_bound_of_diagonal (C : ℝ) (hC : 0 < C)
    (hD : ∀ a b : ℝ, 1 ≤ a → a ≤ b → |tripleRetainedDelta a b| ≤ C*(a/b)*(1+Real.log (b/a)))
    (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) (T X Y : ℝ)
    (hT : 3 ≤ T) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    |tripleRetainedErrorD ω T X Y| ≤ C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y := by
  have hj := tripleBudgetMoment_bounds ω hω T hT 1
  simp only [pow_one] at hj
  have hj0 : 0 ≤ tripleBudgetMoment ω T 1 := (Real.log_nonneg (by linarith : 1 ≤ T)).trans hj.1
  have hy := tripleRetained_delta_term_bound C X Y hX hY hD
  have hx := tripleRetained_delta_term_bound C Y X hY hX hD
  rw [mul_comm Y X] at hx
  have hb : |tripleRetainedDelta X (X*Y)/Y+tripleRetainedDelta Y (X*Y)/X| ≤
      C*tripleRetainedDiagonalScale X Y := by
    exact (abs_add_le _ _).trans ((add_le_add hy hx).trans_eq (by unfold tripleRetainedDiagonalScale; ring))
  unfold tripleRetainedErrorD
  rw [abs_mul,abs_of_nonneg hj0]
  have h := mul_le_mul hj.2 hb (abs_nonneg _) (Real.log_nonneg (by linarith : 1 ≤ 2*T+2))
  exact h.trans_eq (by ring)

/-- One C works before choosing the weight, height, or either prime scale. -/
theorem tripleRetainedErrorD_uniform : ∃ C : ℝ, 0 < C ∧ ∀ (ω : ℝ → ℝ) (T X Y : ℝ),
    TripleBudgetWeight ω → 3 ≤ T → 1 ≤ X → 1 ≤ Y →
    |tripleRetainedErrorD ω T X Y| ≤ C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y := by
  obtain ⟨C,hC,hD⟩ := tripleRetainedDelta_uniform
  exact ⟨C,hC,fun ω T X Y hω hT hX hY =>
    tripleRetainedErrorD_bound_of_diagonal C hC hD ω hω T X Y hT hX hY⟩

/-- The smoothing contribution keeps its explicit sign and constant two. -/
theorem tripleRetainedErrorJ_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 0 < T) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    0 ≤ tripleRetainedErrorJ ω T X Y ∧ tripleRetainedErrorJ ω T X Y ≤ 2*tripleRetainedG X Y/T := by
  have hj := tripleSmoothingError_bounds ω hω T hT
  have hg := tripleRetainedG_nonneg X Y hX hY
  refine ⟨mul_nonneg hj.1 hg,?_⟩
  exact (mul_le_mul_of_nonneg_right hj.2 hg).trans_eq (by ring)

/-- The three additive losses remain separate in the combined norm bound. -/
theorem tripleRetained_combined_bound (C : ℝ) (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3 ≤ T) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hD : |tripleRetainedErrorD ω T X Y| ≤ C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y) :
    ‖tripleBudgetRetained ω T X Y-(tripleRetainedMain ω T X Y:ℂ)‖ ≤
      C*Real.log (2*T+2)*tripleRetainedDiagonalScale X Y+2*tripleRetainedG X Y/T+
      tripleResonanceDecayConstant*tripleResonanceScale (X*Y) := by
  have hj := tripleRetainedErrorJ_bounds ω hω T X Y (by linarith) hX hY
  have hr := triplePrimeResonantMass_decay X Y hX hY
  rw [tripleRetained_residual_norm ω T X Y hX hY]
  calc
    _ ≤ |tripleRetainedErrorD ω T X Y|+|tripleRetainedErrorJ ω T X Y|+|triplePrimeResonantMass X Y| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |tripleRetainedErrorD ω T X Y|+tripleRetainedErrorJ ω T X Y+triplePrimeResonantMass X Y := by
      rw [abs_of_nonneg hj.1,abs_of_nonneg hr.1]
    _ ≤ _ := add_le_add (add_le_add hD hj.2) hr.2

end
end HigherCorrelations
