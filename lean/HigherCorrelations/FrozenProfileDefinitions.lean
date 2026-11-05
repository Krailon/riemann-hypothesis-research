import HigherCorrelations.KernelLocalizationDefinitions

/-! UNCONDITIONAL definition-only frozen coefficients. The master anchor is
slot two; the test anchor is slot zero. Neither coefficient includes a factor eight. -/
namespace HigherCorrelations
noncomputable section

def tripleFrozenProfile (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) : ℂ :=
  (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*tripleAnchoredProfile v

def tripleFrozenTestProfile (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) : ℂ :=
  (ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*actualRationalKernel v

end
end HigherCorrelations
