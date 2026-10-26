import HigherCorrelations.TripleBudgetDefinitions
import HigherCorrelations.PairDiagonalDefinitions

/-! UNCONDITIONAL. Two-scale diagonal definitions. Integer upper endpoints are
inclusive; the middle and tail ranges exclude their lower endpoint. -/
namespace HigherCorrelations
noncomputable section

def tripleMixedDiagonalWeight (a b u : ℝ) : ℝ :=
  if u ≤ a then u/(a*b) else if u ≤ b then a/(b*u) else a*b/u^3

def tripleMixedDiagonalMain (a b : ℝ) : ℝ :=
  a/(2*b)*(1+Real.log (b/a))*Real.log (a*b)

def tripleMixedDiagonalModel (a b : ℝ) : ℝ :=
  tripleMixedDiagonalMain a b+a/b*(1+Real.log (b/a))-1/(4*a*b)

end
end HigherCorrelations
