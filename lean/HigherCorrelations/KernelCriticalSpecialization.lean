import HigherCorrelations.ProfileCriticalExpansion
import HigherCorrelations.KernelLocalizationBounds

/-! UNCONDITIONAL tuplewise critical-line specialization.
Only the three specified occurrences are assumed to be on the line. Repetitions
are permitted. No infinite sum or critical-line assertion about other zeros occurs. -/
namespace HigherCorrelations
noncomputable section
open Set

private theorem critical_height_pos (T : ℝ) (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) : 0<T :=
  lt_of_lt_of_le (by positivity) hT

theorem criticalMasterGap_unscale (T : ℝ) (v : MasterTriple) (i : Fin 3)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) :
    criticalMasterGap T v i/meanSpacing T=occurrenceOrdinate (v i)-occurrenceOrdinate (v 2) := by
  have hl : 0 < meanSpacing T := lt_of_lt_of_le (by norm_num) (microscopic_meanSpacing_ge_one T hT)
  unfold criticalMasterGap
  exact mul_div_cancel_left₀ _ hl.ne'

theorem tripleAnchoredProfile_critical_quadratic_bound (R T : ℝ) (v : MasterTriple) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleAnchoredProfile v-criticalProfileApproximation (meanSpacing T)
      (criticalMasterGap T v 0) (criticalMasterGap T v 1)‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing T)^4 := by
  have h := rationalProfile_critical_microscopic_bound R T _ _ hR hT hu hv
  rw [criticalMasterGap_unscale T v 0 hT,criticalMasterGap_unscale T v 1 hT] at h
  simpa only [tripleAnchoredProfile,hline] using h

theorem tripleAnchoredProfile_critical_leading_bound (R T : ℝ) (v : MasterTriple) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleAnchoredProfile v-kernelBenchmark‖ ≤
      criticalProfileLeadingConstant R/(meanSpacing T)^2 := by
  have h := rationalProfile_critical_leading_bound R (meanSpacing T) _ _ hR
    (microscopic_meanSpacing_ge_one T hT) hu hv
  rw [criticalMasterGap_unscale T v 0 hT,criticalMasterGap_unscale T v 1 hT] at h
  simpa only [tripleAnchoredProfile,hline] using h

private theorem kernel_profile_approximation (ω : ℝ → ℝ) (W M : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) (A : ℂ) (E : ℝ)
    (hb : ‖tripleAnchoredProfile v-A‖≤E) :
    ‖tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*A‖ ≤
      W*E/T+16*Real.pi*M/(27*T^2) := by
  have hE : 0≤E := (norm_nonneg _).trans hb
  have he := tripleKernelLocalizationError_bound_deriv ω M hM hω hd T hT v
  have he' : ‖tripleKernelLocalizationError ω T v‖≤16*Real.pi*M/(27*T^2) := by
    apply he.trans
    calc
      _ ≤ 64*Real.pi*M/(27*T^2*4) := by
        apply div_le_div₀ (by positivity) (le_refl _) (by positivity)
        gcongr
        exact le_add_of_nonneg_right (sq_nonneg _)
      _ = _ := by ring
  have hm : ‖(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*(tripleAnchoredProfile v-A)‖≤W*E/T := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hT]
    calc
      _ ≤ (W/T)*E := by gcongr; exact hw _
      _ = _ := by ring
  have hid : tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*A =
      (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*(tripleAnchoredProfile v-A)+
        tripleKernelLocalizationError ω T v := by
    rw [tripleMasterKernel_localization ω hω.continuous hs T hT v]
    ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hm he')

theorem tripleMasterKernel_critical_quadratic_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*
      criticalProfileApproximation (meanSpacing T) (criticalMasterGap T v 0) (criticalMasterGap T v 1)‖ ≤
      W*criticalProfileRemainderConstant R/(T*(meanSpacing T)^4)+16*Real.pi*M/(27*T^2) := by
  convert kernel_profile_approximation ω W M hW hM hω hs hw hd T (critical_height_pos T hT) v _ _
    (tripleAnchoredProfile_critical_quadratic_bound R T v hR hT hline hu hv) using 1 <;> ring

theorem tripleMasterKernel_critical_leading_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*kernelBenchmark‖ ≤
      W*criticalProfileLeadingConstant R/(T*(meanSpacing T)^2)+16*Real.pi*M/(27*T^2) := by
  convert kernel_profile_approximation ω W M hW hM hω hs hw hd T (critical_height_pos T hT) v _ _
    (tripleAnchoredProfile_critical_leading_bound R T v hR hT hline hu hv) using 1 <;> ring

theorem tripleTestKernel_critical_quadratic_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |meanSpacing T*actualProfileGap v 1|≤R) (hv : |meanSpacing T*actualProfileGap v 2|≤R) :
    ‖tripleMasterKernel ω T (tripleTestToMaster v)-(ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*
      criticalProfileApproximation (meanSpacing T) (meanSpacing T*actualProfileGap v 1)
        (meanSpacing T*actualProfileGap v 2)‖ ≤
      W*criticalProfileRemainderConstant R/(T*(meanSpacing T)^4)+16*Real.pi*M/(27*T^2) := by
  apply tripleMasterKernel_critical_quadratic_bound ω W M R T hW hM hR hω hs hw hd hT (tripleTestToMaster v)
  · intro i; fin_cases i <;> simpa [tripleTestToMaster] using hline _
  · exact hu
  · exact hv

theorem tripleTestKernel_critical_leading_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |meanSpacing T*actualProfileGap v 1|≤R) (hv : |meanSpacing T*actualProfileGap v 2|≤R) :
    ‖tripleMasterKernel ω T (tripleTestToMaster v)-(ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*kernelBenchmark‖ ≤
      W*criticalProfileLeadingConstant R/(T*(meanSpacing T)^2)+16*Real.pi*M/(27*T^2) := by
  apply tripleMasterKernel_critical_leading_bound ω W M R T hW hM hR hω hs hw hd hT (tripleTestToMaster v)
  · intro i; fin_cases i <;> simpa [tripleTestToMaster] using hline _
  · exact hu
  · exact hv


theorem tripleAnchoredProfile_critical_repeated (i : ZeroOccurrence)
    (hi : occurrenceDisplacement i=0) :
    tripleAnchoredProfile (fun _ => i)=kernelBenchmark := by
  simp [tripleAnchoredProfile,hi,rationalProfile_origin]

theorem tripleMasterKernel_critical_zero_weight (T : ℝ) (v : MasterTriple) (ℓ u w : ℝ) :
    tripleMasterKernel (fun _ => 0) T v-(0/T:ℝ)*criticalProfileApproximation ℓ u w=0 := by
  simp [tripleMasterKernel_zero_weight]


end
end HigherCorrelations
