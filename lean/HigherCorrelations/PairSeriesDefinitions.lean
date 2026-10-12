import HigherCorrelations.ZeroOccurrenceDefinitions
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Definition-only interface for PAIR-EF-CONVERGENCE. UNCONDITIONAL.
Positive real powers use exp(log X * z); primes are indexed by n+1.
The zero cutoff is inclusive, and the absolute tail is strictly exterior. -/
namespace HigherCorrelations
noncomputable section

def pairSeriesDomain : Set (ℝ × ℝ) := {p | 1 ≤ p.1}
def pairSeriesRectangle (B H : ℝ) : Set (ℝ × ℝ) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ B ∧ |p.2| ≤ H}

def pairZeroTerm (i : ZeroOccurrence) (p : ℝ × ℝ) : ℂ :=
  2 * Complex.exp ((Real.log p.1 : ℂ) *
    ((occurrenceDisplacement i : ℂ) + Complex.I * (occurrenceOrdinate i - p.2))) /
      (1 + ((p.2 - occurrenceOrdinate i : ℝ) + Complex.I * occurrenceDisplacement i)^2)

def pairPrimeTerm (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
    Complex.exp ((Real.log (n+1 : ℝ) : ℂ) * (-(1/2 : ℂ) - Complex.I * p.2)) *
      (min ((n+1 : ℝ)/p.1) (p.1/(n+1 : ℝ)) : ℝ)

def pairZeroSeries (p : ℝ × ℝ) : ℂ := ∑' i, pairZeroTerm i p
def pairPrimeSeries (p : ℝ × ℝ) : ℂ := ∑' n, pairPrimeTerm n p

def pairZeroTail (X t U : ℝ) : ℝ :=
  ∑' i : {i : ZeroOccurrence // U < |occurrenceOrdinate i|}, ‖pairZeroTerm i.val (X,t)‖

end
end HigherCorrelations
