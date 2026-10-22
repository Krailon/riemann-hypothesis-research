import HigherCorrelations.PairZeroDefinitions

/-! UNCONDITIONAL definition-only normalized pair interface. All occurrence
pairs, multiplicities and the full (0,T] endpoint weight are inherited. -/
namespace HigherCorrelations
noncomputable section

def pairNormalizedCorrelation (T α : ℝ) : ℝ :=
  2*Real.pi*(pairCorrelationSum (T^α) T).re/(T*Real.log T)
def pairNormalizedPeakError (X T : ℝ) : ℝ := pairRHSSmallError X T/(T*Real.log T)
def pairNormalizedMeanError (X T : ℝ) : ℝ := pairRHSLargeError X T/(T*Real.log T)
def pairNormalizedComparisonError (X T : ℝ) : ℝ :=
  (2*Real.pi*(pairCorrelationSum X T).re-pairZeroMeanSquare X T)/(T*Real.log T)

end
end HigherCorrelations
