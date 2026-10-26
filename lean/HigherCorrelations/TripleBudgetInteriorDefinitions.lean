import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.TripleArithmeticDefinitions

/-! UNCONDITIONAL constants for combining the uniform triple budget. -/
namespace HigherCorrelations
noncomputable section

def tripleBudgetHConstant : ℝ := pairArchConstant+pairDSConstant+16

def tripleBudgetInteriorNormConstant (C : ℝ) : ℝ := 1+tripleBudgetHConstant+Real.sqrt (2*C)

def tripleBudgetMixedConstant : ℝ :=
  triplePrimeMassConstant^2/Real.log 2^2+4*Real.sqrt 2*tripleDyadicConstant 3

def tripleBudgetCubicConstant : ℝ :=
  triplePrimeMassConstant^3/Real.log 2^2+4*Real.sqrt 2*Real.sqrt (tripleDyadicConstant 5*tripleDyadicConstant 3)

def tripleBudgetNamedConstant : ℝ :=
  1+triplePrimeMassConstant^2/Real.log 4+30+2*tripleBudgetMixedConstant+tripleBudgetCubicConstant

end
end HigherCorrelations
