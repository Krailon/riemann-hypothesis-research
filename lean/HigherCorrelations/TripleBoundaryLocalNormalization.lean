import HigherCorrelations.TripleBoundaryLocalBound

/-! UNCONDITIONAL normalized residual estimates for local boundary profiles. -/
namespace HigherCorrelations
noncomputable section

private theorem normalize_local_square (q L Z P K : ℝ) (hq : 1 ≤ q)
    (hL : 0 ≤ L) (hZ : 0 < Z) (hP : 0 ≤ P) (hK : 0 ≤ K) (hLK : L ≤ K*q) :
    (L^2/Z+L+P)/q^2 ≤ K^2/Z+K/q+P := by
  have hq0 : 0 < q := by linarith
  have hr : L/q ≤ K := (div_le_iff₀ hq0).mpr hLK
  have hs := pow_le_pow_left₀ (div_nonneg hL hq0.le) hr 2
  have h1 := div_le_div_of_nonneg_right hs hZ.le
  have h2 := div_le_div_of_nonneg_right hr hq0.le
  have h3 : P/q^2 ≤ P := div_le_self hP (by nlinarith)
  convert add_le_add (add_le_add h1 h2) h3 using 1 <;> ring

theorem tripleBoundary_local_square_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 2*Real.pi*Real.exp 1 ≤ T →
    1 ≤ X → 1 ≤ Y → X*Y ≤ T →
    ‖tripleQuadrantRemainder ω T X Y/(Real.log T:ℂ)^2‖ ≤
      C*(1+W+fourierDerivativeL1 ω 1)*
        (tripleBoundaryLogConstant^2/(X*Y)+tripleBoundaryLogConstant/Real.log T+
          (X*Y)/T*Real.log (2*T+2)^4) := by
  obtain ⟨C,hC,h⟩ := tripleBoundary_local_bound
  refine ⟨C,hC,?_⟩
  intro ω hω W T X Y hW hw hT hX hY hZ
  have ht := tripleBoundary_height T hT
  have ht3 := (tripleTestBase_bounds T ht.1).1
  have hq : 1 ≤ Real.log T := by
    rw [ht.2.2.1]
    linarith [ht.2.1,Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  have hq0 : 0 < Real.log T := by linarith
  have hL : 0 ≤ Real.log (2*T+2) := le_trans (by norm_num) (tripleBudget_height_log T ht3)
  have hK := tripleBoundaryLogConstant_pos
  have hLK : Real.log (2*T+2) ≤ tripleBoundaryLogConstant*Real.log T :=
    ht.2.2.2.trans (mul_le_mul_of_nonneg_left (by
      rw [ht.2.2.1]
      linarith [Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]) hK.le)
  have hP : 0 ≤ (X*Y)/T*Real.log (2*T+2)^4 := by positivity
  have hz : 0 < X*Y := by positivity
  have he := h ω hω W T X Y hW hw ht3 hX hY hZ
  rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]
  apply (div_le_div_of_nonneg_right he (sq_nonneg _)).trans
  have hn := normalize_local_square _ _ _ _ _ hq hL hz hP hK.le hLK
  have hw1 := fourierDerivativeL1_nonneg ω 1
  have hh := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ C*(1+W+fourierDerivativeL1 ω 1) by positivity)
  convert hh using 1 <;> ring

theorem tripleBoundary_local_cube_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ W T X Y : ℝ,
    0 ≤ W → (∀ u, ω u ≤ W) → 2*Real.pi*Real.exp 1 ≤ T →
    1 ≤ X → 1 ≤ Y → X*Y ≤ T →
    ‖tripleQuadrantRemainder ω T X Y/(Real.log T:ℂ)^3‖ ≤
      C*(1+W+fourierDerivativeL1 ω 1)*
        ((tripleBoundaryLogConstant^2+tripleBoundaryLogConstant)/Real.log T+
          (X*Y)/T*Real.log (2*T+2)^4) := by
  obtain ⟨C,hC,h⟩ := tripleBoundary_local_square_bound
  refine ⟨C,hC,?_⟩
  intro ω hω W T X Y hW hw hT hX hY hZ
  have ht := tripleBoundary_height T hT
  have hq : 1 ≤ Real.log T := by
    rw [ht.2.2.1]
    linarith [ht.2.1,Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])]
  have hq0 : 0 < Real.log T := by linarith
  have hz : 1 ≤ X*Y := by nlinarith
  have hP : 0 ≤ (X*Y)/T*Real.log (2*T+2)^4 := by
    have ht3 := (tripleTestBase_bounds T ht.1).1
    positivity
  have hK := tripleBoundaryLogConstant_pos
  have he := h ω hω W T X Y hW hw hT hX hY hZ
  have hid : tripleQuadrantRemainder ω T X Y/(Real.log T:ℂ)^3 =
      (tripleQuadrantRemainder ω T X Y/(Real.log T:ℂ)^2)/(Real.log T:ℂ) := by ring
  rw [hid,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hq0]
  apply (div_le_div_of_nonneg_right he hq0.le).trans
  have h1 : tripleBoundaryLogConstant^2/(X*Y) ≤ tripleBoundaryLogConstant^2 :=
    div_le_self (sq_nonneg _) hz
  have h2 : tripleBoundaryLogConstant/Real.log T ≤ tripleBoundaryLogConstant := div_le_self hK.le hq
  have h3 := div_le_self hP hq
  have hh := add_le_add (div_le_div_of_nonneg_right (add_le_add h1 h2) hq0.le) h3
  have hw1 := fourierDerivativeL1_nonneg ω 1
  have hf := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ C*(1+W+fourierDerivativeL1 ω 1) by positivity)
  convert hf using 1 <;> ring

end
end HigherCorrelations
