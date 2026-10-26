import HigherCorrelations.TripleArithmeticDefinitions
import HigherCorrelations.PairSieveDefinitions

/-! UNCONDITIONAL definition-only resonance-decay envelopes. Ball cutoffs are
inclusive. Covers are nonnegative majorants, not disjoint reindexings. -/
namespace HigherCorrelations
noncomputable section

def tripleProperPowerConstant : ℝ := 1+6/Real.log 2

def tripleResonanceScale (Z : ℝ) : ℝ := Real.log (2*Z)^3/Real.sqrt Z

def tripleResonanceMajorant (Z : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ ¬n.Prime then
    tripleMultiplicativeWeight Z n^2*Real.log n^3/n else 0

def tripleResonanceBall (Z R : ℝ) (n : ℕ) : ℝ :=
  if n ≤ ⌊R⌋₊ ∧ IsPrimePow n ∧ ¬n.Prime then
    (8*Z^2/R^3)*Real.log (2*R)^3 else 0

def tripleResonanceDecayConstant : ℝ :=
  8*tripleProperPowerConstant*∑' j : ℕ, (j+1:ℝ)^3*(1/4:ℝ)^j

end
end HigherCorrelations
