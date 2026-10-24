import HigherCorrelations.PairMeanDefinitions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

/-! UNCONDITIONAL definition-only interface for exact Fourier decay.
Derivatives are real derivatives; the project transform is in cycles. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def fourierDerivativeL1 (ω : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∫ u : ℝ, |iteratedDeriv N ω u|

end
end HigherCorrelations
