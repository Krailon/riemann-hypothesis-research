import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.TriplePrimeFourier
import HigherCorrelations.PairDiagonalAsymptotic
import Mathlib.Analysis.MeanInequalities

/-! UNCONDITIONAL mixed prime diagonal, including every prime power. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudgetDiagonal_summable (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun n : ℕ => pairMeanPrimeCoefficient X n*pairMeanPrimeCoefficient Y n) := by
  have hx : Summable (pairMeanPrimeCoefficient X) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (pairMeanPrimeCoefficient_nonneg X hX _)] using pairMeanPrimeCoefficient_summable X hX
  have hy : Summable (pairMeanPrimeCoefficient Y) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (pairMeanPrimeCoefficient_nonneg Y hY _)] using pairMeanPrimeCoefficient_summable Y hY
  have hp : Summable (fun p : ℕ × ℕ => pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient Y p.2) :=
    hx.mul_of_nonneg hy (pairMeanPrimeCoefficient_nonneg X hX) (pairMeanPrimeCoefficient_nonneg Y hY)
  have he := hp.comp_injective
    (show Function.Injective (fun n : ℕ => (n,n)) from fun _ _ h => congrArg Prod.fst h)
  exact he


theorem tripleBudgetDiagonal_nonneg (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    0 ≤ tripleBudgetDiagonal X Y :=
  tsum_nonneg (fun n => mul_nonneg (pairMeanPrimeCoefficient_nonneg X hX n)
    (pairMeanPrimeCoefficient_nonneg Y hY n))

theorem tripleBudgetDiagonal_swap (X Y : ℝ) :
    tripleBudgetDiagonal X Y = tripleBudgetDiagonal Y X := by
  unfold tripleBudgetDiagonal
  simp_rw [mul_comm]

theorem tripleBudgetDiagonal_self (X : ℝ) :
    tripleBudgetDiagonal X X = pairMeanPrimeDiagonal X := by
  simp only [tripleBudgetDiagonal,pairMeanPrimeDiagonal,pow_two]

theorem tripleBudgetDiagonal_cauchy (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    tripleBudgetDiagonal X Y ≤
      Real.sqrt (pairMeanPrimeDiagonal X)*Real.sqrt (pairMeanPrimeDiagonal Y) := by
  have hs (x : ℝ) (hx : 1≤x) : Summable (fun n => pairMeanPrimeCoefficient x n^(2:ℝ)) := by
    have h := pairFrequency_diagonal_summable (fun n => (pairMeanPrimeCoefficient x n:ℂ))
      (pairMeanPrimeCoefficient_summable x hx)
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.rpow_two] using h
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (pairMeanPrimeCoefficient_nonneg X hX) (pairMeanPrimeCoefficient_nonneg Y hY)
    (hs X hX) (hs Y hY)
  simpa only [Real.rpow_two,← Real.sqrt_eq_rpow,tripleBudgetDiagonal,pairMeanPrimeDiagonal] using h

theorem tripleBudgetDiagonal_uniform : ∃ C : ℝ, 0<C ∧ ∀ X Y : ℝ,
    1≤X → 1≤Y → tripleBudgetDiagonal X Y ≤ C*Real.sqrt (Real.log (2*X)*Real.log (2*Y)) := by
  obtain ⟨C,hC,hb⟩ := pairMeanPrimeDiagonal_upper
  refine ⟨C,hC,?_⟩
  intro X Y hX hY
  have hx : 0≤Real.log (2*X) := Real.log_nonneg (by linarith)
  have hy : 0≤Real.log (2*Y) := Real.log_nonneg (by linarith)
  calc
    _ ≤ Real.sqrt (pairMeanPrimeDiagonal X)*Real.sqrt (pairMeanPrimeDiagonal Y) :=
      tripleBudgetDiagonal_cauchy X Y hX hY
    _ ≤ Real.sqrt (C*Real.log (2*X))*Real.sqrt (C*Real.log (2*Y)) := by
      gcongr <;> exact hb _ ‹_›
    _ = _ := by
      rw [Real.sqrt_mul hC.le,Real.sqrt_mul hC.le,Real.sqrt_mul hx]
      calc
        _ = (Real.sqrt C)^2 * (Real.sqrt (Real.log (2*X))*Real.sqrt (Real.log (2*Y))) := by ring
        _ = _ := by rw [Real.sq_sqrt hC.le]

end
end HigherCorrelations
