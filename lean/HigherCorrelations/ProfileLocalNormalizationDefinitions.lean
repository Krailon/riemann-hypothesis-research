import HigherCorrelations.RationalTransferDefinitions

/-! UNCONDITIONAL definition-only coefficient of the local critical-line kernel
relative to the project ordinate normalization. Analytic statements use T>2pi. -/
namespace HigherCorrelations
noncomputable section

def criticalLocalCoefficient (T : ℝ) : ℝ :=
  3*Real.log (T/(2*Real.pi))/(2*Real.log T)

end
end HigherCorrelations
