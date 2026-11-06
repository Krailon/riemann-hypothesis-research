import HigherCorrelations.KernelLocalizationDefinitions

/-! UNCONDITIONAL definition-only critical-parameter expansion interface.
These definitions specialize parameters, not the global zero population. -/
namespace HigherCorrelations
noncomputable section

def criticalGapQuadratic (u v : ℝ) : ℝ := u^2+v^2-u*v

def criticalProfileRemainderConstant (R : ℝ) : ℝ := Real.pi*(R^4+R^6+R^8)

def criticalProfileLeadingConstant (R : ℝ) : ℝ :=
  15*Real.pi*R^2/32+criticalProfileRemainderConstant R

def criticalProfileApproximation (ℓ u v : ℝ) : ℂ :=
  ((3*Real.pi/8-5*Real.pi*criticalGapQuadratic u v/(32*ℓ^2) : ℝ) : ℂ)

def criticalMasterGap (T : ℝ) (v : MasterTriple) (i : Fin 3) : ℝ :=
  meanSpacing T*(occurrenceOrdinate (v i)-occurrenceOrdinate (v 2))

end
end HigherCorrelations
