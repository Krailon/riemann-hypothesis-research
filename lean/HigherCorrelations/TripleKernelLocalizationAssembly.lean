import HigherCorrelations.KernelLocalizationBounds
import HigherCorrelations.KernelLocalizationSummed
import HigherCorrelations.ProfileTransferLimits
import HigherCorrelations.ProfileMicroscopicLimits
import HigherCorrelations.KernelCriticalSpecialization

/-! UNCONDITIONAL exact, tuplewise and summed kernel localization, including
absolute unweighted and complex-test weighted frozen-profile convergence.
Normalized correlation transfer and fixed-test height limits are included.
The effective microscopic profile limit and the critical-parameter quadratic
expansion with tuplewise critical-line bounds are also included. The ordinate-only
signed error and effectiveness of the summed counting constants remain separate. -/
namespace HigherCorrelations
noncomputable section
open Set
open scoped NNReal

theorem tripleKernelLocalizationError_zero (T : ℝ) (v : MasterTriple) :
    tripleKernelLocalizationError (fun _ => 0) T v=0 := by
  simp [tripleKernelLocalizationError,tripleKernelLocalizationIntegrand]

theorem tripleAnchoredProfile_repeated (i : ZeroOccurrence) :
    tripleAnchoredProfile (fun _ => i) = rationalProfile 0 0
      (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by
  simp [tripleAnchoredProfile]

theorem tripleMasterKernel_localization_bound (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hd : ∀ x, |deriv ω x|≤M) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleMasterKernel ω T v-
      (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*tripleAnchoredProfile v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by
  rw [tripleMasterKernel_localization ω hω.continuous hs T hT v, add_sub_cancel_left]
  exact tripleKernelLocalizationError_bound_deriv ω M hM hω hd T hT v

theorem tripleTestKernel_localization_bound (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hd : ∀ x, |deriv ω x|≤M) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleMasterKernel ω T (tripleTestToMaster v)-
      (ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*actualRationalKernel v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))^2)) :=
  tripleMasterKernel_localization_bound ω M hM hω hs hd T hT (tripleTestToMaster v)

theorem tripleKernelLocalizationError_equal_ordinates (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple)
    (hg : occurrenceOrdinate (v 0)=occurrenceOrdinate (v 1)) :
    ‖tripleKernelLocalizationError ω T v‖ ≤ 16*Real.pi*(M:ℝ)/(27*T^2) := by
  have h := tripleKernelLocalizationError_bound ω M hω T hT v
  rw [hg, sub_self] at h
  convert h using 1
  ring


end
end HigherCorrelations
