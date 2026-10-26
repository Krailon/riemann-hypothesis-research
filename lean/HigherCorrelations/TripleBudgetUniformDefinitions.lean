import HigherCorrelations.TripleBudgetInteriorDefinitions

/-! UNCONDITIONAL definition-only two-branch prime norm envelope. -/
namespace HigherCorrelations
noncomputable section

def tripleBudgetPrimeB (x : ℝ) : ℝ := triplePrimeMassConstant*Real.sqrt x*Real.log (2*x)

def tripleBudgetPrimeM (C W T x : ℝ) : ℝ :=
  if x≤2*T then min (tripleBudgetPrimeB x) (Real.sqrt (2*C*W*Real.log (2*x)))
  else tripleBudgetPrimeB x

end
end HigherCorrelations
