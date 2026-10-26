import HigherCorrelations.TripleMixedDiagonalDefinitions
import HigherCorrelations.TripleSmoothingMomentDefinitions
import HigherCorrelations.TripleResonanceDecayDefinitions

/-! UNCONDITIONAL retained-term definitions. Delta orders its two arguments;
all named errors are real, while the existing retained observable is complex. -/
namespace HigherCorrelations
noncomputable section

def tripleRetainedDelta (a b : ℝ) : ℝ :=
  tripleBudgetDiagonal a b-tripleMixedDiagonalMain (min a b) (max a b)

def tripleRetainedG (X Y : ℝ) : ℝ :=
  (1+Real.log Y)*Real.log (X*(X*Y))/(2*Y^2)+
  (1+Real.log X)*Real.log (Y*(X*Y))/(2*X^2)

def tripleRetainedDiagonalScale (X Y : ℝ) : ℝ :=
  (1+Real.log Y)/Y^2+(1+Real.log X)/X^2

def tripleRetainedErrorD (ω : ℝ → ℝ) (T X Y : ℝ) : ℝ :=
  tripleBudgetMoment ω T 1*(tripleRetainedDelta X (X*Y)/Y+tripleRetainedDelta Y (X*Y)/X)

def tripleRetainedErrorJ (ω : ℝ → ℝ) (T X Y : ℝ) : ℝ :=
  tripleSmoothingError ω T*tripleRetainedG X Y

def tripleRetainedMain (ω : ℝ → ℝ) (T X Y : ℝ) : ℝ :=
  Real.log T^3/(X*Y)^2+(Real.log T+tripleSmoothingMean ω)*tripleRetainedG X Y

end
end HigherCorrelations
