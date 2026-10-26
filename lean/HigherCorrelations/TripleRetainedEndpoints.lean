import HigherCorrelations.TripleRetainedEvaluation

/-! UNCONDITIONAL symmetry and endpoint checks. No limiting extension is used
at unit scales, equal scales, or the closed height endpoint T=3. -/
namespace HigherCorrelations
noncomputable section

theorem tripleRetainedMain_swap (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleRetainedMain ω T X Y = tripleRetainedMain ω T Y X := by
  unfold tripleRetainedMain
  rw [mul_comm Y X,tripleRetainedG_swap X Y]

theorem triplePrimeResonantMass_swap (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    triplePrimeResonantMass X Y = triplePrimeResonantMass Y X := by
  rw [← tripleArithmetic_resonance_sum X Y hX hY,← tripleArithmetic_resonance_sum Y X hY hX,
    (tripleArithmetic_resonance_summable X Y hX hY).tsum_prod,
    (tripleArithmetic_resonance_summable Y X hY hX).tsum_prod]
  simp only [Prod.fst,Prod.snd]
  rw [← Summable.tsum_comm (f := fun m n : ℕ => tripleArithmeticCoefficient X m*
    tripleArithmeticCoefficient Y n*tripleArithmeticCoefficient (X*Y) (m*n))
    (tripleArithmetic_resonance_summable X Y hX hY)]
  apply tsum_congr; intro n
  apply tsum_congr; intro m
  rw [mul_comm Y X,Nat.mul_comm n m]
  ring

theorem tripleBudgetRetained_swap (ω : ℝ → ℝ) (T X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    tripleBudgetRetained ω T X Y = tripleBudgetRetained ω T Y X := by
  rw [tripleRetained_exact ω T X Y hX hY,tripleRetained_exact ω T Y X hY hX,
    tripleRetainedMain_swap ω T X Y,tripleRetainedErrorD_swap ω T X Y,
    tripleRetainedErrorJ_swap ω T X Y,triplePrimeResonantMass_swap X Y hX hY]

theorem tripleRetainedDelta_self (X : ℝ) (hX : 1 ≤ X) :
    tripleRetainedDelta X X = pairMeanPrimeDiagonal X-Real.log X := by
  rw [tripleRetainedDelta_ordered X X le_rfl,tripleBudgetDiagonal_self,tripleMixedDiagonalMain_self X hX]

theorem tripleRetainedG_self (X : ℝ) (hX : 1 ≤ X) :
    tripleRetainedG X X = 3*(1+Real.log X)*Real.log X/X^2 := by
  have hx : X ≠ 0 := by linarith
  unfold tripleRetainedG
  rw [Real.log_mul hx (mul_ne_zero hx hx),Real.log_mul hx hx]
  ring

theorem tripleRetainedG_unit_left (Y : ℝ) (hY : 1 ≤ Y) :
    tripleRetainedG 1 Y = (1+Real.log Y)*Real.log Y/(2*Y^2)+Real.log Y := by
  have hy : Y ≠ 0 := by linarith
  simp only [tripleRetainedG,one_mul,Real.log_one,add_zero,one_pow,mul_one,Real.log_mul hy hy]
  ring

theorem tripleRetainedG_unit_right (X : ℝ) (hX : 1 ≤ X) :
    tripleRetainedG X 1 = (1+Real.log X)*Real.log X/(2*X^2)+Real.log X := by
  rw [tripleRetainedG_swap X 1]
  exact tripleRetainedG_unit_left X hX

theorem tripleRetained_unit_values (ω : ℝ → ℝ) (T : ℝ) :
    tripleRetainedG 1 1 = 0 ∧ tripleRetainedDiagonalScale 1 1 = 2 ∧
    tripleRetainedErrorJ ω T 1 1 = 0 := by
  norm_num [tripleRetainedG,tripleRetainedDiagonalScale,tripleRetainedErrorJ]

theorem tripleRetained_unit_identity (ω : ℝ → ℝ) (T : ℝ) :
    tripleBudgetRetained ω T 1 1 =
      (Real.log T^3+2*tripleBudgetMoment ω T 1*pairMeanPrimeDiagonal 1-triplePrimeResonantMass 1 1 : ℝ) := by
  rw [tripleRetained_exact ω T 1 1 (by norm_num) (by norm_num)]
  simp only [tripleRetainedMain,tripleRetainedErrorD,tripleRetainedErrorJ,
    (tripleRetained_unit_values ω T).1,mul_zero,one_mul,one_pow,div_one,add_zero,
    tripleRetainedDelta_self 1 (by norm_num),Real.log_one,sub_zero]
  congr 1
  ring

theorem tripleRetained_height_three : ∃ C : ℝ, 0 < C ∧ ∀ (ω : ℝ → ℝ) (X Y : ℝ),
    TripleBudgetWeight ω → 1 ≤ X → 1 ≤ Y →
    |tripleRetainedErrorD ω 3 X Y| ≤ C*Real.log 8*tripleRetainedDiagonalScale X Y ∧
    (0 ≤ tripleRetainedErrorJ ω 3 X Y ∧ tripleRetainedErrorJ ω 3 X Y ≤ 2*tripleRetainedG X Y/3) := by
  obtain ⟨C,hC,h⟩ := tripleRetained_evaluation
  refine ⟨C,hC,?_⟩
  intro ω X Y hω hX hY
  have he := h ω 3 X Y hω (by norm_num) hX hY
  refine ⟨?_,he.2.2.2.2.1⟩
  convert he.2.2.2.1 using 1 <;> norm_num

end
end HigherCorrelations
