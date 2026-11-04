import HigherCorrelations.KernelLocalizationDefinitions
import Mathlib.MeasureTheory.Group.Integral

/-! UNCONDITIONAL independent expected statements for exact localization only.
Intentional holes are confined to verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleAnchoredProfile_denominators (v : MasterTriple) (u : ℝ) :
    (tripleMasterDenominator (v 0) (occurrenceOrdinate (v 2)+u)*
      tripleMasterDenominator (v 1) (occurrenceOrdinate (v 2)+u)*
      star (tripleMasterDenominator (v 2) (occurrenceOrdinate (v 2)+u)))⁻¹ =
        tripleAnchoredProfileIntegrand v u := by sorry

theorem tripleMasterKernelIntegrand_translate (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) (u : ℝ) :
    tripleMasterKernelIntegrand ω T v (occurrenceOrdinate (v 2)+u) =
      (ω ((occurrenceOrdinate (v 2)+u)/T)/T:ℝ)*tripleAnchoredProfileIntegrand v u := by sorry

theorem tripleAnchoredProfile_integrable (v : MasterTriple) :
    Integrable (tripleAnchoredProfileIntegrand v) := by sorry

theorem tripleAnchoredProfile_integral (v : MasterTriple) :
    (∫ u : ℝ, tripleAnchoredProfileIntegrand v u)=tripleAnchoredProfile v := by sorry

theorem tripleAnchoredProfile_test_order (v : MasterTriple) :
    tripleAnchoredProfile (tripleTestToMaster v)=actualRationalKernel v := by sorry

theorem tripleKernel_weighted_profile_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (fun u : ℝ => (ω ((occurrenceOrdinate (v 2)+u)/T):ℂ)*
      tripleAnchoredProfileIntegrand v u) := by sorry

theorem tripleKernel_frozen_profile_integrable (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    Integrable (fun u : ℝ => (ω (occurrenceOrdinate (v 2)/T):ℂ)*
      tripleAnchoredProfileIntegrand v u) := by sorry

theorem tripleKernelLocalizationIntegrand_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (tripleKernelLocalizationIntegrand ω T v) := by sorry

theorem tripleKernelLocalizationError_absolutely_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (fun u => ‖(1/(T:ℂ))*tripleKernelLocalizationIntegrand ω T v u‖) := by sorry

theorem tripleMasterKernel_anchored_integral (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel ω T v = (1/(T:ℂ))*∫ u : ℝ,
      (ω ((occurrenceOrdinate (v 2)+u)/T):ℂ)*tripleAnchoredProfileIntegrand v u := by sorry

theorem tripleMasterKernel_localization (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleMasterKernel ω T v =
      (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*tripleAnchoredProfile v+
        tripleKernelLocalizationError ω T v := by sorry

theorem tripleTestKernel_localization (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleMasterKernel ω T (tripleTestToMaster v) =
      (ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*actualRationalKernel v+
        tripleKernelLocalizationError ω T (tripleTestToMaster v) := by sorry

theorem tripleKernelLocalizationError_zero (T : ℝ) (v : MasterTriple) :
    tripleKernelLocalizationError (fun _ => 0) T v=0 := by sorry

theorem tripleAnchoredProfile_repeated (i : ZeroOccurrence) :
    tripleAnchoredProfile (fun _ => i) = rationalProfile 0 0
      (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by sorry

end
end HigherCorrelations
