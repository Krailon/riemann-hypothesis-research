import HigherCorrelations.KernelLocalizationDefinitions
import HigherCorrelations.IntegralProfile
import HigherCorrelations.TripleMasterIdentity
import Mathlib.MeasureTheory.Group.Integral

/-! UNCONDITIONAL exact localization at fixed positive height.
Each weighted profile is integrable before subtraction. No triple sum or
height limit is taken here. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

theorem tripleAnchoredProfile_denominators (v : MasterTriple) (u : ℝ) :
    (tripleMasterDenominator (v 0) (occurrenceOrdinate (v 2)+u)*
      tripleMasterDenominator (v 1) (occurrenceOrdinate (v 2)+u)*
      star (tripleMasterDenominator (v 2) (occurrenceOrdinate (v 2)+u)))⁻¹ =
        tripleAnchoredProfileIntegrand v u := by
  simp only [tripleMasterDenominator,tripleAnchoredProfileIntegrand,profileIntegrand,
    scalarKernel,Complex.star_def,map_add,map_one,map_pow,map_mul,
    Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,mul_inv_rev]
  push_cast
  ring

theorem tripleMasterKernelIntegrand_translate (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) (u : ℝ) :
    tripleMasterKernelIntegrand ω T v (occurrenceOrdinate (v 2)+u) =
      (ω ((occurrenceOrdinate (v 2)+u)/T)/T:ℝ)*tripleAnchoredProfileIntegrand v u := by
  rw [tripleMasterKernelIntegrand,div_eq_mul_inv,tripleAnchoredProfile_denominators]

theorem tripleAnchoredProfile_integrable (v : MasterTriple) :
    Integrable (tripleAnchoredProfileIntegrand v) := by
  apply profileIntegrand_integrable <;>
    exact le_trans (occurrence_displacement_lt _).le (by norm_num)

theorem tripleAnchoredProfile_integral (v : MasterTriple) :
    (∫ u : ℝ, tripleAnchoredProfileIntegrand v u)=tripleAnchoredProfile v := by
  apply integralProfile_eq <;>
    exact le_trans (occurrence_displacement_lt _).le (by norm_num)

theorem tripleAnchoredProfile_test_order (v : MasterTriple) :
    tripleAnchoredProfile (tripleTestToMaster v)=actualRationalKernel v := rfl

theorem tripleKernel_weighted_profile_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (fun u : ℝ => (ω ((occurrenceOrdinate (v 2)+u)/T):ℂ)*
      tripleAnchoredProfileIntegrand v u) := by
  have hi := (tripleMasterKernel_integrable ω hω hs T hT v).comp_add_left (occurrenceOrdinate (v 2))
  simp_rw [tripleMasterKernelIntegrand_translate] at hi
  have hh := hi.const_mul (T:ℂ)
  convert hh using 1
  funext u
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']

theorem tripleKernel_frozen_profile_integrable (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    Integrable (fun u : ℝ => (ω (occurrenceOrdinate (v 2)/T):ℂ)*
      tripleAnchoredProfileIntegrand v u) :=
  (tripleAnchoredProfile_integrable v).const_mul _

theorem tripleKernelLocalizationIntegrand_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (tripleKernelLocalizationIntegrand ω T v) := by
  have h := (tripleKernel_weighted_profile_integrable ω hω hs T hT v).sub
    (tripleKernel_frozen_profile_integrable ω T v)
  convert h using 1
  funext u
  simp [tripleKernelLocalizationIntegrand,sub_mul]

theorem tripleKernelLocalizationError_absolutely_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (fun u => ‖(1/(T:ℂ))*tripleKernelLocalizationIntegrand ω T v u‖) :=
  ((tripleKernelLocalizationIntegrand_integrable ω hω hs T hT v).const_mul _).norm

theorem tripleMasterKernel_anchored_integral (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel ω T v = (1/(T:ℂ))*∫ u : ℝ,
      (ω ((occurrenceOrdinate (v 2)+u)/T):ℂ)*tripleAnchoredProfileIntegrand v u := by
  rw [tripleMasterKernel,← integral_add_left_eq_self _ (occurrenceOrdinate (v 2))]
  simp_rw [tripleMasterKernelIntegrand_translate]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  push_cast
  ring

theorem tripleMasterKernel_localization (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleMasterKernel ω T v =
      (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*tripleAnchoredProfile v+
        tripleKernelLocalizationError ω T v := by
  have he : (∫ u : ℝ, tripleKernelLocalizationIntegrand ω T v u) =
      (∫ u : ℝ, (ω ((occurrenceOrdinate (v 2)+u)/T):ℂ)*tripleAnchoredProfileIntegrand v u)-
      (ω (occurrenceOrdinate (v 2)/T):ℂ)*tripleAnchoredProfile v := by
    simp only [tripleKernelLocalizationIntegrand,Complex.ofReal_sub,sub_mul]
    rw [integral_sub (tripleKernel_weighted_profile_integrable ω hω hs T hT v)
      (tripleKernel_frozen_profile_integrable ω T v),integral_const_mul,tripleAnchoredProfile_integral]
  rw [tripleMasterKernel_anchored_integral,tripleKernelLocalizationError,he]
  push_cast
  ring

theorem tripleTestKernel_localization (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleMasterKernel ω T (tripleTestToMaster v) =
      (ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*actualRationalKernel v+
        tripleKernelLocalizationError ω T (tripleTestToMaster v) :=
  tripleMasterKernel_localization ω hω hs T hT (tripleTestToMaster v)

end
end HigherCorrelations
