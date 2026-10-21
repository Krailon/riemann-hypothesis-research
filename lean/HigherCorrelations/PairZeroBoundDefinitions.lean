import HigherCorrelations.PairZeroDefinitions
import Mathlib.Data.Finset.Max
import HigherCorrelations.UniformHeightDefinitions

/-! UNCONDITIONAL definition-only finite-height envelope. Zero is included so
an empty cutoff has envelope zero. No quantitative zero-free region is used. -/
namespace HigherCorrelations
noncomputable section

def pairZeroHorizontalValues (Z : ℝ) : Finset ℝ := by
  classical
  exact insert 0 ((occurrenceCutoff Z).image occurrenceDisplacement)
def pairZeroHorizontalEnvelope (Z : ℝ) : ℝ :=
  (pairZeroHorizontalValues Z).max' (by
    classical
    exact Finset.insert_nonempty _ _)
def pairZeroBoundaryProfile (T t : ℝ) : ℝ := 1/(1+t)+1/(1+T-t)
def pairZeroExtensionProfile (T t : ℝ) : ℝ := (1+heightIntervalDistance T t)⁻¹^2

end
end HigherCorrelations
