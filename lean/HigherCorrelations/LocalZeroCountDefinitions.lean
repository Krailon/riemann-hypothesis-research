import HigherCorrelations.ZeroOccurrenceDefinitions
import Mathlib.Data.Finset.Sigma
import Mathlib.Analysis.Complex.JensenFormula

/-! Definition-only closed interval counts. UNCONDITIONAL.
All analytic multiplicities and both interval endpoints are retained. -/
namespace HigherCorrelations
noncomputable section

def stripZeroInterval (v w : ℝ) : Finset StripZero := by
  classical
  exact if h : Set.Finite {ρ : StripZero | v ≤ ρ.val.im ∧ ρ.val.im ≤ w}
    then h.toFinset else ∅

def occurrenceInterval (v w : ℝ) : Finset ZeroOccurrence :=
  (stripZeroInterval v w).sigma (fun _ρ => Finset.univ)

def rightStripZeroInterval (v w : ℝ) : Finset StripZero := by
  classical
  exact (stripZeroInterval v w).filter (fun ρ => 1/2 ≤ ρ.val.re)

def jensenCenter (t : ℝ) : ℂ := 2 + Complex.I*t

def localJensenMass (t : ℝ) : ℝ :=
  ((∑ᶠ z : ℂ, MeromorphicOn.divisor riemannZeta
    (Metric.closedBall (jensenCenter t) (8/5)) z : ℤ) : ℝ)

end
end HigherCorrelations
