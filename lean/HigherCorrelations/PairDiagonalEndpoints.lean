import HigherCorrelations.PairDiagonalAsymptotic
import HigherCorrelations.PairDiagonalPowerBound

/-! UNCONDITIONAL. Uniform diagonal theorem and exact endpoint conventions.
The constants here are existential; no effective PNT threshold is claimed. -/
namespace HigherCorrelations
noncomputable section
open scoped ArithmeticFunction.vonMangoldt

theorem pairMeanPrimeDiagonal_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-Real.log X| ≤ C ∧
    pairMeanPrimeDiagonal X ≤ C*Real.log (2*X) ∧
    0 ≤ pairMeanPrimePowerDiagonal X ∧
    pairMeanPrimePowerDiagonal X ≤ C*pairDiagonalPowerScale X ∧
    pairMeanPrimePowerDiagonal X ≤ C := by
  obtain ⟨A,hA,ha⟩ := pairMeanPrimeDiagonal_asymptotic
  obtain ⟨B,hB,hb⟩ := pairMeanPrimeDiagonal_upper
  obtain ⟨P,hP,hp⟩ := pairMeanPrimePowerDiagonal_sharp
  obtain ⟨Q,hQ,hq⟩ := pairMeanPrimePowerDiagonal_bounded
  refine ⟨A+B+P+Q, by positivity, ?_⟩
  intro X hX
  have hl : 0 ≤ Real.log (2*X) := Real.log_nonneg (by linarith)
  have hs : 0 ≤ pairDiagonalPowerScale X := by unfold pairDiagonalPowerScale; positivity
  refine ⟨(ha X hX).trans (by linarith), (hb X hX).trans ?_,
    pairMeanPrimePowerDiagonal_nonneg X, (hp X hX).trans ?_, (hq X hX).trans (by linarith)⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hl
  · exact mul_le_mul_of_nonneg_right (by linarith) hs

theorem pairMeanPrimeDiagonal_unit : ∃ C : ℝ, 0 < C ∧ pairMeanPrimeDiagonal 1 ≤ C := by
  obtain ⟨C,hC,hb⟩ := pairMeanPrimeDiagonal_asymptotic
  refine ⟨C,hC,?_⟩
  simpa only [Real.log_one,sub_zero,abs_of_nonneg (pairMeanPrimeDiagonal_nonneg 1)] using hb 1 le_rfl

/-- At an integer cutoff, including every proper prime power, the term belongs
only to the inclusive head. Both algebraic expressions for its weight agree. -/
theorem pairDiagonal_cutoff_term (n : ℕ) (hn : 1 ≤ n) :
    pairDiagonalWeight n n*(Λ n)^2 = (Λ n)^2/(n:ℝ) ∧
    (if (n:ℝ) < n then (Λ n)^2/(n:ℝ)^3 else 0) = 0 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  constructor
  · simp only [pairDiagonalWeight,le_refl,ite_true]
    field_simp
  · simp

/-- Translation of the square-root denominator to the stated X^{-1/2} scale. -/
theorem pairDiagonalPowerScale_rpow (X : ℝ) (hX : 0 < X) :
    pairDiagonalPowerScale X = X^(-(1/2:ℝ))*Real.log (2*X)^3 := by
  unfold pairDiagonalPowerScale
  rw [Real.rpow_neg hX.le,← Real.sqrt_eq_rpow]
  ring

end
end HigherCorrelations
