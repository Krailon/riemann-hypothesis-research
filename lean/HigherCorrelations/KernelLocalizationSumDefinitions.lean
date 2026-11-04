import HigherCorrelations.KernelLocalizationDefinitions
import HigherCorrelations.UniformHeightDefinitions

/-! UNCONDITIONAL regional localization definitions. The near region includes
its distance boundary; the center interval includes both height endpoints. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

inductive LocalizationRegion where
  | near | farCenter | farAnchor
  deriving DecidableEq

def localizationRegionSet (r : LocalizationRegion) (T c : ℝ) : Set ℝ :=
  match r with
  | .near => {t | |t-c| ≤ T}
  | .farCenter => {t | T < |t-c| ∧ t ∈ Icc T (2*T)}
  | .farAnchor => {t | T < |t-c| ∧ t ∉ Icc T (2*T) ∧ c ∈ Icc T (2*T)}

def localizationErrorDensity (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) (t : ℝ) : ℂ :=
  (1/(T:ℂ))*tripleKernelLocalizationIntegrand ω T v (t-occurrenceOrdinate (v 2))

def localizationRegionalDensity (r : LocalizationRegion) (ω : ℝ → ℝ) (T : ℝ)
    (v : MasterTriple) : ℝ → ℂ :=
  (localizationRegionSet r T (occurrenceOrdinate (v 2))).indicator
    (localizationErrorDensity ω T v)

def localizationRegionalError (r : LocalizationRegion) (ω : ℝ → ℝ) (T : ℝ)
    (v : MasterTriple) : ℂ := ∫ t : ℝ, localizationRegionalDensity r ω T v t

def localizationRegionalMass (r : LocalizationRegion) (ω : ℝ → ℝ) (T : ℝ)
    (v : MasterTriple) : ℝ := ∫ t : ℝ, ‖localizationRegionalDensity r ω T v t‖

def localizationAnchorWeight (r : LocalizationRegion) (ω : ℝ → ℝ) (T t : ℝ)
    (i : ZeroOccurrence) : ℝ :=
  (localizationRegionSet r T (occurrenceOrdinate i)).indicator
    (fun t => ordinateKernel (t-occurrenceOrdinate i)*|ω (t/T)-ω (occurrenceOrdinate i/T)|) t

def localizationTailProfile (u : ℝ) : ℝ :=
  (1+Real.log (3*|u|+2)^2)/(1+u^2)

end
end HigherCorrelations
