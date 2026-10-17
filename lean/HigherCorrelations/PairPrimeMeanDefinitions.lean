import HigherCorrelations.PairMeanPrimeDefinitions
import HigherCorrelations.PairSeriesDefinitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! UNCONDITIONAL definition-only interface for the optimized prime mean square.
The off-diagonal error includes the diagonal cost of the Fourier majorants. -/
namespace HigherCorrelations
noncomputable section

def pairPrimeMeanBandwidth (X T : ℝ) : ℝ := (1/2)*Real.sqrt (Real.log (2*X)/(T*X))
def pairPrimeMeanSquare (X T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, ‖pairPrimeSeries (X,t)‖^2
def pairPrimeMeanOffdiag (X T : ℝ) : ℝ := pairPrimeMeanSquare X T-T*pairMeanPrimeDiagonal X
def pairPrimeMeanDiagonalError (X T : ℝ) : ℝ := T*pairMeanPrimeDiagonal X-T*Real.log X
def pairPrimeMeanL2Norm (X T : ℝ) : ℝ := Real.sqrt (pairPrimeMeanSquare X T)

end
end HigherCorrelations
