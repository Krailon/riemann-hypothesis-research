import HigherCorrelations.PairMeanPrimeDefinitions
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! UNCONDITIONAL. Definition-only interfaces for the prime diagonal milestone.
All integer cutoffs are inclusive; index k in the coefficient API denotes k+1. -/
namespace HigherCorrelations
noncomputable section
open scoped ArithmeticFunction.vonMangoldt

def pairDiagonalWeight (X u : ℝ) : ℝ := if u ≤ X then u/X^2 else X^2/u^3

def pairDiagonalCumulative (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, (Λ n)^2

def pairDiagonalPowerCumulative (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, if IsPrimePow n ∧ ¬n.Prime then (Λ n)^2 else 0

def pairMeanPrimePowerDiagonal (X : ℝ) : ℝ :=
  ∑' k : ℕ, if IsPrimePow (k+1) ∧ ¬(k+1).Prime then
    pairMeanPrimeCoefficient X k^2 else 0

/-- Finite nonnegative dyadic cover; overlaps are intentional. -/
def pairDiagonalPowerBall (X R : ℝ) (n : ℕ) : ℝ :=
  if n ≤ ⌊R⌋₊ ∧ IsPrimePow n ∧ ¬n.Prime then (8*X^2/R^3)*(Λ n)^2 else 0

def pairDiagonalPowerScale (X : ℝ) : ℝ := Real.log (2*X)^3 / Real.sqrt X

end
end HigherCorrelations
