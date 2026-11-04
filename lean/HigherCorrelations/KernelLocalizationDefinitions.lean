import HigherCorrelations.TripleTestDefinitions
import HigherCorrelations.IntegralProfileDefinitions

/-! UNCONDITIONAL definition-only kernel localization interface.
Master slots are j,k,l, with slot 2 the conjugated anchor. The error is an
explicit weight-difference integral, not a definition by subtraction of kernels. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def tripleAnchoredProfileIntegrand (v : MasterTriple) (u : ℝ) : ℂ :=
  profileIntegrand (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))
    (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))
    (occurrenceDisplacement (v 0)) (occurrenceDisplacement (v 1))
    (occurrenceDisplacement (v 2)) u

def tripleAnchoredProfile (v : MasterTriple) : ℂ :=
  rationalProfile (occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2))
    (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))
    (occurrenceDisplacement (v 0)) (occurrenceDisplacement (v 1))
    (occurrenceDisplacement (v 2))

def tripleKernelLocalizationIntegrand (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) (u : ℝ) : ℂ :=
  ((ω ((occurrenceOrdinate (v 2)+u)/T)-ω (occurrenceOrdinate (v 2)/T):ℝ):ℂ)*
    tripleAnchoredProfileIntegrand v u

def tripleKernelLocalizationError (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) : ℂ :=
  (1/(T:ℂ))*∫ u : ℝ, tripleKernelLocalizationIntegrand ω T v u

end
end HigherCorrelations
