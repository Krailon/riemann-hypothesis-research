import HigherCorrelations.PairDiagonalDefinitions
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! UNCONDITIONAL statement specifications. Unfinished challenge proofs are
isolated from the solution import graph. Constants are existential. -/
namespace HigherCorrelations
noncomputable section
open Finset Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Topology

theorem pairMeanPrimeCoefficient_sq_weight (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    pairMeanPrimeCoefficient X n^2 = pairDiagonalWeight X (n+1)*(Λ (n+1))^2 := by sorry

theorem pairMeanPrimeDiagonal_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun n => pairMeanPrimeCoefficient X n^2) := by sorry

theorem pairMeanPrimeDiagonal_split (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimeDiagonal X =
      (1/X^2)*(∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (n:ℝ)*(Λ n)^2) +
      X^2*(∑' n : ℕ, if X < (n:ℝ) then (Λ n)^2/(n:ℝ)^3 else 0) := by sorry

theorem pairDiagonal_partial_tendsto (X : ℝ) (hX : 1 ≤ X) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 0 N, pairDiagonalWeight X n*(Λ n)^2)
      atTop (nhds (pairMeanPrimeDiagonal X)) := by sorry

theorem pairMeanPrimeDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-Real.log X| ≤ C := by sorry

theorem pairMeanPrimeDiagonal_upper : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimeDiagonal X ≤ C*Real.log (2*X) := by sorry

theorem pairDiagonalCumulative_bound : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ u →
    |pairDiagonalCumulative u-u*Real.log u| ≤ C*u := by sorry

theorem pairMeanPrimeDiagonal_uniform : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    |pairMeanPrimeDiagonal X-Real.log X| ≤ C ∧
    pairMeanPrimeDiagonal X ≤ C*Real.log (2*X) ∧
    0 ≤ pairMeanPrimePowerDiagonal X ∧
    pairMeanPrimePowerDiagonal X ≤ C*pairDiagonalPowerScale X ∧
    pairMeanPrimePowerDiagonal X ≤ C := by sorry

theorem pairMeanPrimeDiagonal_unit : ∃ C : ℝ, 0 < C ∧ pairMeanPrimeDiagonal 1 ≤ C := by sorry

theorem pairDiagonal_cutoff_term (n : ℕ) (hn : 1 ≤ n) :
    pairDiagonalWeight n n*(Λ n)^2 = (Λ n)^2/(n:ℝ) ∧
    (if (n:ℝ) < n then (Λ n)^2/(n:ℝ)^3 else 0) = 0 := by sorry

theorem pairDiagonalPowerScale_rpow (X : ℝ) (hX : 0 < X) :
    pairDiagonalPowerScale X = X^(-(1/2:ℝ))*Real.log (2*X)^3 := by sorry

theorem pairDiagonal_finite_error_bound (C X Y : ℝ) (hC : 0 < C) (hX : 1 ≤ X) (hXY : X ≤ Y)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ C*u) :
    |(∑ n ∈ Icc 0 ⌊Y⌋₊, pairDiagonalWeight X n*(Λ n)^2)-
      (Real.log X+1-1/(4*X^2)-X^2*(2*Real.log Y+3)/(4*Y^2))| ≤ 3*C := by sorry

theorem pairDiagonalPNT_log_error : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 ≤ u →
    |Chebyshev.psi u-u| *Real.log u ≤ C*u := by sorry

theorem pairDiagonalPowerBall_double_summable (X : ℝ) (hX : 1 ≤ X) :
    Summable (fun q : ℕ × ℕ => pairDiagonalPowerBall X ((2:ℝ)^q.1*X) q.2) := by sorry

theorem pairMeanPrimePowerDiagonal_sharp : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimePowerDiagonal X ≤ C*pairDiagonalPowerScale X := by sorry

theorem pairMeanPrimePowerDiagonal_bounded : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    pairMeanPrimePowerDiagonal X ≤ C := by sorry

theorem pairDiagonalPowerCumulative_bound (u : ℝ) (hu : 1 ≤ u) :
    pairDiagonalPowerCumulative u ≤ (4/Real.log 2)*Real.sqrt u*Real.log (2*u)^3 := by sorry
end
end HigherCorrelations
