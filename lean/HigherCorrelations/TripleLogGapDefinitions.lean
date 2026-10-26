import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! UNCONDITIONAL definition-only reciprocal-log interface, on integers at least two. -/
namespace HigherCorrelations
noncomputable section

abbrev LogGapIndex := {n : ℕ // 2≤n}

def tripleLogMass (c : LogGapIndex → ℂ) : ℝ := ∑' n, ‖c n‖

def tripleLogEnergyTerm (c : LogGapIndex → ℂ) (n : LogGapIndex) : ℝ :=
  (n.val:ℝ)*Real.log (2*n.val)*‖c n‖^2

def tripleLogEnergy (c : LogGapIndex → ℂ) : ℝ := ∑' n, tripleLogEnergyTerm c n

def tripleLogGapTerm (c d : LogGapIndex → ℂ) (p : LogGapIndex × LogGapIndex) : ℝ :=
  if p.1=p.2 then 0 else ‖c p.1*d p.2‖/|Real.log ((p.1.val:ℝ)/p.2.val)|

def tripleLogGapBound (c d : LogGapIndex → ℂ) : ℝ :=
  tripleLogMass c*tripleLogMass d/Real.log 2 +
    4*Real.sqrt 2*Real.sqrt (tripleLogEnergy c*tripleLogEnergy d)

def tripleComparableKernel (m n : ℕ) : ℝ :=
  if m≤2*n ∧ n≤2*m ∧ m≠n then 1/|(m:ℝ)-n| else 0

end
end HigherCorrelations
