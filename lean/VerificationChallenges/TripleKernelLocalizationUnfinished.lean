import HigherCorrelations.KernelLocalizationDefinitions
import HigherCorrelations.KernelLocalizationSumDefinitions
import HigherCorrelations.FrozenProfileDefinitions
import HigherCorrelations.SignedSectorDefinitions
import HigherCorrelations.ProfileTransferDefinitions
import HigherCorrelations.ProfileMicroscopicDefinitions
import HigherCorrelations.ProfileCriticalDefinitions
import HigherCorrelations.ProfileZeroGapDefinitions
import HigherCorrelations.ProfileLocalNormalizationDefinitions
import HigherCorrelations.TripleBoundaryDefinitions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.MeanValue

/-! UNCONDITIONAL independent expected statements for exact, tuplewise and summed localization.
Intentional holes are confined to verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

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

theorem scalar_denominator_half_strip (x e : ℝ) (he : |e| ≤ 1/2) :
    (3/4:ℝ)*(1+x^2) ≤ ‖1+((x:ℂ)+Complex.I*e)^2‖ := by sorry

theorem scalarKernel_half_strip_bound (x e : ℝ) (he : |e| ≤ 1/2) :
    ‖scalarKernel x e‖ ≤ (4/3:ℝ)/(1+x^2) := by sorry

theorem localization_pair_majorant_integrable (a b : ℝ) :
    Integrable (fun u : ℝ => 1/((1+(u-a)^2)*(1+(u-b)^2))) := by sorry

theorem localization_pair_majorant_integral (a b : ℝ) :
    (∫ u : ℝ, 1/((1+(u-a)^2)*(1+(u-b)^2))) =
      2*Real.pi/(4+(a-b)^2) := by sorry

theorem localization_anchor_moment_bound (u : ℝ) :
    |u|/(1+u^2) ≤ (1/2:ℝ) := by sorry

theorem profileIntegrand_localization_moment (a b e f g u : ℝ)
    (he : |e| ≤ 1/2) (hf : |f| ≤ 1/2) (hg : |g| ≤ 1/2) :
    |u| *‖profileIntegrand a b e f g u‖ ≤
      (32/27:ℝ)*(1/((1+(u-a)^2)*(1+(u-b)^2))) := by sorry

theorem localization_weight_difference (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T c u : ℝ) (hT : 0<T) :
    |ω ((c+u)/T)-ω (c/T)| ≤ (M:ℝ)/T*|u| := by sorry

theorem tripleKernelLocalizationIntegrand_bound (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) (u : ℝ) :
    ‖tripleKernelLocalizationIntegrand ω T v u‖ ≤
      (32*(M:ℝ)/(27*T))*(1/((1+(u-(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 2)))^2)*
        (1+(u-(occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2)))^2))) := by sorry

theorem tripleKernelLocalizationIntegrand_integrable_lipschitz (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (tripleKernelLocalizationIntegrand ω T v) := by sorry

theorem tripleKernelLocalizationError_bound (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤
      64*Real.pi*(M:ℝ)/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by sorry

theorem tripleKernelLocalizationError_bound_deriv (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hd : ∀ x, |deriv ω x|≤M)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by sorry

theorem localizationRegion_measurable (r : LocalizationRegion) (T c : ℝ) :
    MeasurableSet (localizationRegionSet r T c) := by sorry

theorem localizationRegion_disjoint (T c : ℝ) :
    Disjoint (localizationRegionSet .near T c) (localizationRegionSet .farCenter T c) ∧
    Disjoint (localizationRegionSet .near T c) (localizationRegionSet .farAnchor T c) ∧
    Disjoint (localizationRegionSet .farCenter T c) (localizationRegionSet .farAnchor T c) := by sorry

theorem localization_weight_zero (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 0<T)
    (ht : t ∉ Icc T (2*T)) : ω (t/T)=0 := by sorry

theorem localizationErrorDensity_integrable (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (localizationErrorDensity ω T v) := by sorry

theorem localizationRegionalDensity_integrable (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (localizationRegionalDensity r ω T v) := by sorry

theorem localizationErrorDensity_integral (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    (∫ t : ℝ, localizationErrorDensity ω T v t) = tripleKernelLocalizationError ω T v := by sorry

theorem localizationRegionalDensity_partition (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T)
    (v : MasterTriple) (t : ℝ) :
    localizationErrorDensity ω T v t =
      localizationRegionalDensity .near ω T v t+
      localizationRegionalDensity .farCenter ω T v t+
      localizationRegionalDensity .farAnchor ω T v t := by sorry

theorem localizationRegionalError_partition (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleKernelLocalizationError ω T v = localizationRegionalError .near ω T v+
      localizationRegionalError .farCenter ω T v+localizationRegionalError .farAnchor ω T v := by sorry

theorem localizationRegionalMass_nonneg (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (v : MasterTriple) : 0 ≤ localizationRegionalMass r ω T v := by sorry

theorem localizationRegionalError_norm_le (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (v : MasterTriple) :
    ‖localizationRegionalError r ω T v‖ ≤ localizationRegionalMass r ω T v := by sorry

theorem localization_log_ge_one (T : ℝ) (hT : 3≤T) : 1≤Real.log (2*T+2) := by sorry

theorem localization_local_log (T x : ℝ) (hT : 3≤T) (hx : |x|≤4*T+2) :
    Real.log (|x|+2) ≤ 2*Real.log (2*T+2) := by sorry

theorem localization_unit_shell_weight (u : ℝ) (n : ℕ) (hn : (n:ℝ)≤|u|) :
    |u| *ordinateKernel u ≤ 2/((n:ℝ)+1) := by sorry

theorem localization_near_moment_finite :
    ∃ C : ℝ, 0<C ∧ ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) →
      ∀ s : Finset ZeroOccurrence, (∀ i ∈ s, |t-occurrenceOrdinate i|≤T) →
      (∑ i ∈ s, |t-occurrenceOrdinate i| *ordinateKernel (t-occurrenceOrdinate i)) ≤
        C*Real.log (2*T+2)^2 := by sorry

theorem localizationTailProfile_nonneg (u : ℝ) : 0≤localizationTailProfile u := by sorry

theorem localizationTailProfile_integrable : Integrable localizationTailProfile := by sorry

theorem localization_tail_scaled_bound (T c t : ℝ) (hT : 3≤T)
    (hc : c ∈ Icc T (2*T)) (ht : T< |t-c|) :
    Real.log (|t|+2)^2*ordinateKernel (t-c) ≤
      (4*Real.log (2*T+2)^2/T^2)*localizationTailProfile ((t-c)/T) := by sorry

theorem localization_scaled_profile_integrable (T c : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ => localizationTailProfile ((t-c)/T)) := by sorry

theorem localization_scaled_profile_integral (T c : ℝ) (hT : 0<T) :
    (∫ t : ℝ, localizationTailProfile ((t-c)/T)) = T*∫ u : ℝ, localizationTailProfile u := by sorry

theorem localizationAnchorWeight_nonneg (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T t : ℝ) (i : ZeroOccurrence) : 0≤localizationAnchorWeight r ω T t i := by sorry

theorem localizationRegionalDensity_majorant (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) (t : ℝ) :
    ‖localizationRegionalDensity r ω T v t‖ ≤ (64/(27*T)) *
      (ordinateKernel (t-occurrenceOrdinate (v 0))*ordinateKernel (t-occurrenceOrdinate (v 1))*
        localizationAnchorWeight r ω T t (v 2)) := by sorry

theorem localization_finite_product (D : Finset MasterTriple) (s : Finset ZeroOccurrence)
    (hs : ∀ v ∈ D, ∀ r, v r ∈ s) (t : ℝ) (f : ZeroOccurrence → ℝ) (hf : ∀ i, 0≤f i) :
    (∑ v ∈ D, ordinateKernel (t-occurrenceOrdinate (v 0))*
      ordinateKernel (t-occurrenceOrdinate (v 1))*f (v 2)) ≤
      (zeroKernelSum t)^2*(∑ i ∈ s, f i) := by sorry

theorem localization_finite_majorant (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hT : 0<T) (D : Finset MasterTriple) (s : Finset ZeroOccurrence)
    (hs : ∀ v ∈ D, ∀ r, v r ∈ s) (t : ℝ) :
    (∑ v ∈ D, ‖localizationRegionalDensity r ω T v t‖) ≤
      (64/(27*T))*(zeroKernelSum t)^2*(∑ i ∈ s, localizationAnchorWeight r ω T t i) := by sorry

theorem localization_near_weight_zero (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 0<T)
    (ht : t ∉ Icc 0 (3*T)) (i : ZeroOccurrence) :
    localizationAnchorWeight .near ω T t i=0 := by sorry

theorem localization_near_anchor_sum :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) → ∀ s : Finset ZeroOccurrence,
      (∑ i ∈ s, localizationAnchorWeight .near ω T t i) ≤
        C*(M:ℝ)*Real.log (2*T+2)^2/T := by sorry

theorem localization_far_center_anchor_sum :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ), 0≤M → (∀ x, |ω x|≤M) →
      ∀ T t : ℝ, 3≤T → t ∈ Icc T (2*T) → ∀ s : Finset ZeroOccurrence,
      (∑ i ∈ s, localizationAnchorWeight .farCenter ω T t i) ≤
        C*M*Real.log (2*T+2)/T := by sorry

theorem localization_Q_nonneg (t : ℝ) : 0≤zeroKernelSum t := by sorry

theorem localization_Q_local :
    ∃ C : ℝ, 0<C ∧ ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) →
      zeroKernelSum t ≤ C*Real.log (2*T+2) := by sorry

theorem localization_anchor_count :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 3≤T →
      ((occurrenceInterval T (2*T)).card:ℝ) ≤ C*T*Real.log (2*T+2) := by sorry

theorem localization_mass_of_indicator_bound (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T)
    (D : Finset MasterTriple) (a b A : ℝ) (hab : a≤b)
    (hb : ∀ t, (∑ v ∈ D, ‖localizationRegionalDensity r ω T v t‖) ≤ (Icc a b).indicator (fun _ => A) t) :
    (∑ v ∈ D, localizationRegionalMass r ω T v) ≤ (b-a)*A := by sorry

theorem localization_near_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .near ω T v) ≤
        C*(M:ℝ)*Real.log (2*T+2)^4/T := by sorry

theorem localization_far_center_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .farCenter ω T v) ≤
        C*M₀*Real.log (2*T+2)^3/T := by sorry

theorem localization_far_anchor_weight (Q : ℝ) (hQ : 0<Q)
    (hq : ∀ t, zeroKernelSum t ≤ Q*Real.log (|t|+2))
    (ω : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hw : ∀ x, |ω x|≤M)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 3≤T) (i : ZeroOccurrence) :
    (zeroKernelSum t)^2*localizationAnchorWeight .farAnchor ω T t i ≤
      (if i ∈ occurrenceInterval T (2*T) then
        (4*Q^2*M*Real.log (2*T+2)^2/T^2)*localizationTailProfile ((t-occurrenceOrdinate i)/T) else 0) := by sorry

theorem localization_far_anchor_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .farAnchor ω T v) ≤
        C*M₀*Real.log (2*T+2)^3/T := by sorry

theorem localizationRegionalMass_summable_of_finite (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T B : ℝ) (hb : ∀ D : Finset MasterTriple, (∑ v ∈ D, localizationRegionalMass r ω T v)≤B) :
    Summable (localizationRegionalMass r ω T) ∧ (∑' v, localizationRegionalMass r ω T v)≤B := by sorry

theorem localizationRegionalError_summable_bound (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hm : Summable (localizationRegionalMass r ω T)) :
    Summable (fun v => ‖localizationRegionalError r ω T v‖) ∧
      (∑' v, ‖localizationRegionalError r ω T v‖) ≤ ∑' v, localizationRegionalMass r ω T v := by sorry

theorem localizationRegional_sum_integral (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T)
    (hm : Summable (localizationRegionalMass r ω T)) :
    (∑' v, localizationRegionalError r ω T v) = ∫ t : ℝ, ∑' v, localizationRegionalDensity r ω T v t := by sorry

theorem localization_near_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (localizationRegionalMass .near ω T) ∧
      (∑' v, localizationRegionalMass .near ω T v) ≤ C*(M:ℝ)*Real.log (2*T+2)^4/T := by sorry

theorem localization_far_center_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → ∀ T : ℝ, 3≤T →
      Summable (localizationRegionalMass .farCenter ω T) ∧
      (∑' v, localizationRegionalMass .farCenter ω T v) ≤ C*M₀*Real.log (2*T+2)^3/T := by sorry

theorem localization_far_anchor_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (localizationRegionalMass .farAnchor ω T) ∧
      (∑' v, localizationRegionalMass .farAnchor ω T v) ≤ C*M₀*Real.log (2*T+2)^3/T := by sorry

theorem localization_total_error_le_masses (ω : ℝ → ℝ) (M : ℝ≥0)
    (hw : LipschitzWith M ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤ localizationRegionalMass .near ω T v+
      localizationRegionalMass .farCenter ω T v+localizationRegionalMass .farAnchor ω T v := by sorry

theorem tripleKernelLocalizationError_summed_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleKernelLocalizationError ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) ≤
        C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by sorry

theorem tripleKernelLocalizationError_summed_bound_deriv :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ →
      (∀ x, |ω x|≤M₀) → Differentiable ℝ ω → (∀ x, |deriv ω x|≤M₁) →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleKernelLocalizationError ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) ≤
        C*(M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by sorry

theorem tripleFrozenProfile_test_order (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenProfile ω T (tripleTestToMaster v)=tripleFrozenTestProfile ω T v := by sorry

theorem tripleFrozenProfile_eq_sub (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleFrozenProfile ω T v=tripleMasterKernel ω T v-tripleKernelLocalizationError ω T v := by sorry

theorem tripleFrozenProfile_norm_le (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleFrozenProfile ω T v‖≤‖tripleMasterKernel ω T v‖+‖tripleKernelLocalizationError ω T v‖ := by sorry

theorem tripleFrozen_weight_mass_bound (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (M : ℝ) (hM : 0≤M)
    (hb : ∀ u, |ω u|≤M) : (∫ u : ℝ, |ω u|)≤M := by sorry

theorem tripleFrozen_kernel_mass_bound :
    ∃ A : ℝ, 0<A ∧ ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ M : ℝ, 0≤M → (∀ u, |ω u|≤M) → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖)≤A*M*Real.log (2*T+2)^3 := by sorry

theorem tripleFrozenProfile_summable_bound :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by sorry

theorem tripleFrozenProfile_norm_summable (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) := by sorry

theorem tripleFrozenProfile_mass_triangle (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
      (∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖)+
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) := by sorry

theorem tripleFrozenProfile_summable_bound_deriv :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ →
      (∀ u, |ω u|≤M₀) → Differentiable ℝ ω → (∀ u, |deriv ω u|≤M₁) →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*(M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by sorry

theorem tripleFrozenTestProfile_summable_bound :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleFrozenTestProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenTestProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by sorry

theorem tripleFrozenProfile_sum_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, tripleMasterKernel ω T v) =
      (∑' v : MasterTriple, tripleFrozenProfile ω T v)+
      (∑' v : MasterTriple, tripleKernelLocalizationError ω T v) := by sorry

theorem tripleFrozenTestProfile_sum_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)) =
      (∑' v : MasterTriple, tripleFrozenTestProfile ω T v)+
      (∑' v : MasterTriple, tripleKernelLocalizationError ω T (tripleTestToMaster v)) := by sorry

theorem tripleFrozenProfile_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, tripleFrozenProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenProfile ω T v)) := by sorry

theorem tripleFrozenProfile_height_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), tripleFrozenProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenProfile ω T v)) := by sorry

theorem tripleFrozenTestProfile_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, tripleFrozenTestProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenTestProfile ω T v)) := by sorry

theorem tripleFrozenProfile_zero (T : ℝ) (v : MasterTriple) :
    tripleFrozenProfile (fun _ => 0) T v=0 := by sorry

theorem tripleFrozenProfile_repeated (ω : ℝ → ℝ) (T : ℝ) (i : ZeroOccurrence) :
    tripleFrozenProfile ω T (fun _ => i) = (ω (occurrenceOrdinate i/T)/T:ℝ)*
      rationalProfile 0 0 (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by sorry

theorem signedTest_integrand_bound (φ : ℝ × ℝ → ℂ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ)
    (v : MasterTriple) (p : ℝ × ℝ) :
    ‖φ p*Complex.exp (2*Real.pi*Complex.I*
      ((tripleTestArguments T v).1*p.1+(tripleTestArguments T v).2*p.2))‖ ≤
        ‖φ p‖*(tripleTestBase T)^(1-κ) := by sorry

theorem signedTest_integrable (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) (v : MasterTriple) :
    Integrable (fun p : ℝ × ℝ => φ p*Complex.exp (2*Real.pi*Complex.I*
      ((tripleTestArguments T v).1*p.1+(tripleTestArguments T v).2*p.2))) := by sorry

theorem signedTest_bound (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) (v : MasterTriple) :
    ‖complexFourier φ (tripleTestArguments T v)‖ ≤ tripleTestL1 φ*(tripleTestBase T)^(1-κ) := by sorry

theorem signedTest_weighted_summable_bound (f : MasterTriple → ℂ)
    (hf : Summable (fun v => ‖f v‖)) (D : ℝ) (hD : (∑' v, ‖f v‖)≤D)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ)
    (hT : 2*Real.pi<T) (hs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v => ‖f v*complexFourier φ (tripleTestArguments T v)‖) ∧
    (∑' v, ‖f v*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*D := by sorry

theorem tripleFrozenTestProfile_weighted_bound :
    ∃ A C : ℝ, 0<A ∧ 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
      tsupport φ ⊆ signedMargin κ →
      Summable (fun v : MasterTriple =>
        ‖tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)‖) ∧
      (∑' v : MasterTriple,
        ‖tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*
        (A*M₀*Real.log (2*T+2)^3+C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T) := by sorry

theorem tripleTestKernel_weighted_bound :
    ∃ A : ℝ, 0<A ∧ ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ M : ℝ, 0≤M → (∀ u, |ω u|≤M) →
      ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
      tsupport φ ⊆ signedMargin κ →
      Summable (fun v : MasterTriple =>
        ‖tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ∧
      (∑' v : MasterTriple,
        ‖tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*(A*M*Real.log (2*T+2)^3) := by sorry

theorem tripleLocalizationError_weighted_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
      tsupport φ ⊆ signedMargin κ →
      Summable (fun v : MasterTriple =>
        ‖tripleKernelLocalizationError ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ∧
      (∑' v : MasterTriple,
        ‖tripleKernelLocalizationError ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*
        (C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T) := by sorry

theorem tripleFrozenTestProfile_weighted_summable (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v : MasterTriple =>
      ‖tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)‖) := by sorry

theorem tripleFrozenTestProfile_weighted_independent_cutoff
    (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0) (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀)
    (hω : LipschitzWith M₁ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S,
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (∑' v : MasterTriple,
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))) := by sorry

theorem tripleFrozenTestProfile_weighted_height_cutoff
    (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0) (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀)
    (hω : LipschitzWith M₁ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (∑' v : MasterTriple,
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))) := by sorry

theorem tripleFrozenTestProfile_weighted_zero_test (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenTestProfile ω T v*complexFourier (fun _ => 0) (tripleTestArguments T v)=0 := by sorry

theorem tripleFrozenTestProfile_weighted_zero_weight (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenTestProfile (fun _ => 0) T v*complexFourier φ (tripleTestArguments T v)=0 := by sorry

theorem tripleFrozenTestProfile_weighted_repeated (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (T : ℝ) (i : ZeroOccurrence) :
    tripleFrozenTestProfile ω T (fun _ => i)*complexFourier φ (tripleTestArguments T (fun _ => i)) =
      ((ω (occurrenceOrdinate i/T)/T:ℝ):ℂ)*
        rationalProfile 0 0 (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i)*
          complexFourier φ (tripleTestArguments T (fun _ => i)) := by sorry

theorem frozenStatistic_profile_formula (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    frozenStatistic ω φ T = (8/((T:ℂ)*(Real.log T:ℂ)))*
      ∑' v : MasterTriple, (ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*
        complexFourier φ (tripleTestArguments T v) := by sorry

theorem frozenStatistic_transfer_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T-frozenStatistic ω φ T=frozenTransferError ω φ T := by sorry

theorem frozenStatistic_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (8/(Real.log T:ℂ))*
      ∑ v ∈ tripleDomain S, tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))
      atTop (𝓝 (frozenStatistic ω φ T)) := by sorry

theorem frozenStatistic_height_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => (8/(Real.log T:ℂ))*
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))
      atTop (𝓝 (frozenStatistic ω φ T)) := by sorry

theorem frozenStatistic_zero_test (ω : ℝ → ℝ) (T : ℝ) :
    frozenStatistic ω (fun _ => 0) T=0 := by sorry

theorem frozenStatistic_zero_weight (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    frozenStatistic (fun _ => 0) φ T=0 := by sorry

theorem frozenTransferError_raw_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
    tsupport φ ⊆ signedMargin κ →
    ‖frozenTransferError ω φ T‖ ≤
      8*C*tripleTestL1 φ*(tripleTestBase T)^(1-κ)/(T*Real.log T)*
        ((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3) := by sorry

theorem profileTransfer_power_scale (κ T : ℝ) (hT : 2*Real.pi<T) :
    (tripleTestBase T)^(1-κ)/T=(tripleTestBase T)^(-κ)/(2*Real.pi) := by sorry

theorem profileTransfer_height_bounds (T : ℝ) (hT : 2*Real.pi*Real.exp 1≤T) :
    1≤Real.log T ∧ Real.log (2*T+2)≤tripleBoundaryLogConstant*Real.log T := by sorry

theorem profileTransfer_log_budget (M₀ M₁ T : ℝ) (hM₀ : 0≤M₀) (hM₁ : 0≤M₁)
    (hT : 2*Real.pi*Real.exp 1≤T) :
    (M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/Real.log T ≤
      (tripleBoundaryLogConstant+1)*(M₀+M₁)*Real.log (2*T+2)^3 := by sorry

theorem frozenTransferError_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖frozenTransferError ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+(M₁:ℝ))*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem frozenStatistic_transfer_bound : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ → (∀ u, |ω u|≤M₀) →
    LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-frozenStatistic ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+(M₁:ℝ))*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem frozenStatistic_transfer_bound_deriv : ∃ C : ℝ, 0<C ∧
    ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ → (∀ u, |ω u|≤M₀) →
    Differentiable ℝ ω → (∀ u, |deriv ω u|≤M₁) → Function.support ω ⊆ Icc (1:ℝ) 2 →
    ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi*Real.exp 1≤T →
    tsupport φ ⊆ signedMargin κ →
    ‖signedStatistic ω φ T-frozenStatistic ω φ T‖ ≤ C*tripleTestL1 φ*(M₀+M₁)*
      (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem profileTransfer_envelope_tendsto (κ : ℝ) (hκ : 0<κ) :
    Tendsto (fun T : ℝ => (tripleTestBase T)^(-κ)*Real.log (2*T+2)^3) atTop (𝓝 0) := by sorry

theorem frozenTransferError_tendsto (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenTransferError ω φ) atTop (𝓝 0) := by sorry

theorem frozenStatistic_transfer_tendsto (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ : ℝ) (hκ : 0<κ) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun T => signedStatistic ω φ T-frozenStatistic ω φ T) atTop (𝓝 0) := by sorry

theorem profileTransfer_smoothing_bounds (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω) :
    ∃ (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ ∧ (∀ u, |ω u|≤M₀) ∧ LipschitzWith M₁ ω := by sorry

theorem frozenStatistic_uniform_bound : ∃ A C : ℝ, 0<A ∧ 0<C ∧
    ∀ (ω : ℝ → ℝ), TripleBudgetWeight ω → ∀ (M₀ : ℝ) (M₁ : ℝ≥0),
    0≤M₀ → (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω →
    ∀ (φ : ℝ × ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ κ T : ℝ, 0<κ → 2*Real.pi*Real.exp 1≤T → tsupport φ ⊆ signedMargin κ →
    ‖frozenStatistic ω φ T-signedLimit φ‖ ≤
      A*signedC1 φ*(1+M₀+fourierDerivativeL1 ω 1)*
        (1/Real.log (tripleTestBase T)+(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3)+
      C*tripleTestL1 φ*(M₀+(M₁:ℝ))*(tripleTestBase T)^(-κ)*Real.log (2*T+2)^3 := by sorry

theorem frozenStatistic_fixed_margin_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0<κ) (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 (signedLimit φ)) := by sorry

theorem frozenStatistic_compact_limit (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ signedRegion) :
    Tendsto (frozenStatistic ω φ) atTop (𝓝 (signedLimit φ)) := by sorry

theorem profileGapFactor_denominator_ne (x h : ℝ) (hh : |h|≤1) :
    4+((x:ℂ)-Complex.I*h)^2≠0 := by sorry

theorem profileGapFactor_norm_bound (x h : ℝ) (hh : |h|≤1) :
    ‖profileGapFactor x h‖≤(1:ℝ)/3 := by sorry

theorem profileGapFactor_difference (x h : ℝ) (hh : |h|≤1) :
    ‖profileGapFactor x h-profileGapFactor 0 h‖≤(|x|+2)*|x|/9 := by sorry

theorem profileReciprocalSum_difference (p q r p' q' r' : ℂ)
    (hp' : ‖p'‖≤(1:ℝ)/3) (hq : ‖q‖≤(1:ℝ)/3)
    (hq' : ‖q'‖≤(1:ℝ)/3) (hr : ‖r‖≤(1:ℝ)/3) :
    ‖profileReciprocalSum p q r-profileReciprocalSum p' q' r'‖ ≤
      2*(‖p-p'‖+‖q-q'‖+‖r-r'‖) := by sorry

theorem rationalProfile_eq_gap_factors (a b e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    rationalProfile a b e f g = (Real.pi:ℂ)*profileReciprocalSum
      (profileGapFactor (a-b) (e-f)) (profileGapFactor a (e+g)) (profileGapFactor b (f+g)) := by sorry

theorem profileGapFactor_difference_bounded (R x h : ℝ) (hR : 0≤R)
    (hx : |x|≤2*R) (hh : |h|≤1) :
    ‖profileGapFactor x h-profileGapFactor 0 h‖≤(2*R+2)*|x|/9 := by sorry

theorem rationalProfile_gap_bound (R a b e f g : ℝ) (hR : 0≤R)
    (ha : |a|≤R) (hb : |b|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile a b e f g-rationalProfile 0 0 e f g‖ ≤
      (8*Real.pi*(R+1)/9)*(|a|+|b|) := by sorry

theorem rationalProfile_scaled_gap_bound (R ℓ u v e f g : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (v/ℓ) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by sorry

theorem microscopic_meanSpacing_ge_one (T : ℝ) (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) :
    1≤ meanSpacing T := by sorry

theorem microscopic_meanSpacing_tendsto : Tendsto meanSpacing atTop atTop := by sorry

theorem rationalProfile_microscopic_bound (R T u v e f g : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/meanSpacing T := by sorry

theorem rationalProfile_microscopic_tendstoUniformlyOn (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun T (p : Fin 5 → ℝ) => rationalProfile (p 0/meanSpacing T) (p 1/meanSpacing T) (p 2) (p 3) (p 4))
      (fun p => rationalProfile 0 0 (p 2) (p 3) (p 4)) atTop (profileMicroscopicBox R) := by sorry

theorem rationalProfile_microscopic_zero_gaps (ℓ e f g : ℝ) :
    rationalProfile (0/ℓ) (0/ℓ) e f g=rationalProfile 0 0 e f g := by sorry

theorem rationalProfile_microscopic_zero_radius (ℓ u v e f g : ℝ)
    (hu : |u|≤0) (hv : |v|≤0) :
    rationalProfile (u/ℓ) (v/ℓ) e f g=rationalProfile 0 0 e f g := by sorry

theorem rationalProfile_microscopic_coincident_gaps (R ℓ u e f g : ℝ) (hR : 0≤R)
    (hℓ : 1≤ℓ) (hu : |u|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (u/ℓ) e f g-rationalProfile 0 0 e f g‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by sorry

theorem rationalProfile_microscopic_closed_endpoints (R ℓ u v : ℝ) (hR : 0≤R)
    (hℓ : 1≤ℓ) (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) (1/2) (-1/2) (1/2)-rationalProfile 0 0 (1/2) (-1/2) (1/2)‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by sorry

theorem criticalGapQuadratic_nonneg (u v : ℝ) : 0≤criticalGapQuadratic u v := by sorry

theorem criticalGapQuadratic_bound (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) : criticalGapQuadratic u v≤3*R^2 := by sorry

theorem criticalGapQuadratic_div (u v ℓ : ℝ) :
    criticalGapQuadratic (u/ℓ) (v/ℓ)=criticalGapQuadratic u v/ℓ^2 := by sorry

theorem criticalProfileRemainderConstant_nonneg (R : ℝ) :
    0≤criticalProfileRemainderConstant R := by sorry

theorem rationalProfile_critical_remainder_identity (a b : ℝ) :
    rationalProfile a b 0 0 0-criticalProfileApproximation 1 a b =
      ((Real.pi*((7/2:ℝ)*(criticalGapQuadratic a b)^2+
        (5/8:ℝ)*(criticalGapQuadratic a b)^3-(3/8:ℝ)*(a^2*b^2*(a-b)^2)+
        (5/32:ℝ)*criticalGapQuadratic a b*(a^2*b^2*(a-b)^2))/
        ((4+(a-b)^2)*(4+a^2)*(4+b^2)) : ℝ) : ℂ) := by sorry

theorem rationalProfile_critical_remainder_bound (R a b : ℝ) (hR : 0≤R)
    (ha : |a|≤R) (hb : |b|≤R) :
    ‖rationalProfile a b 0 0 0-criticalProfileApproximation 1 a b‖ ≤
      criticalProfileRemainderConstant R := by sorry

theorem rationalProfile_critical_scaled_bound (R ℓ u v : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) 0 0 0-criticalProfileApproximation ℓ u v‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 := by sorry

theorem rationalProfile_critical_microscopic_bound (R T u v : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) 0 0 0-
      criticalProfileApproximation (meanSpacing T) u v‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing T)^4 := by sorry

theorem rationalProfile_critical_leading_bound (R ℓ u v : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/ℓ) (v/ℓ) 0 0 0-kernelBenchmark‖ ≤
      criticalProfileLeadingConstant R/ℓ^2 := by sorry

theorem rationalProfile_critical_zero_radius (ℓ u v : ℝ) (hu : |u|≤0) (hv : |v|≤0) :
    rationalProfile (u/ℓ) (v/ℓ) 0 0 0=criticalProfileApproximation ℓ u v := by sorry

theorem rationalProfile_critical_coincident_bound (R ℓ u : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) :
    ‖rationalProfile (u/ℓ) (u/ℓ) 0 0 0-criticalProfileApproximation ℓ u u‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 := by sorry

theorem rationalProfile_critical_scale_endpoint (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile u v 0 0 0-criticalProfileApproximation 1 u v‖ ≤
      criticalProfileRemainderConstant R := by sorry

theorem rationalProfile_critical_height_endpoint (R u v : ℝ) (hR : 0≤R)
    (hu : |u|≤R) (hv : |v|≤R) :
    ‖rationalProfile (u/meanSpacing (2*Real.pi*Real.exp (2*Real.pi)))
      (v/meanSpacing (2*Real.pi*Real.exp (2*Real.pi))) 0 0 0-
      criticalProfileApproximation (meanSpacing (2*Real.pi*Real.exp (2*Real.pi))) u v‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing (2*Real.pi*Real.exp (2*Real.pi)))^4 := by sorry

theorem rationalProfile_critical_gap_endpoints (R ℓ : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ) :
    ‖rationalProfile (R/ℓ) (-R/ℓ) 0 0 0-criticalProfileApproximation ℓ R (-R)‖ ≤
      criticalProfileRemainderConstant R/ℓ^4 := by sorry

theorem criticalMasterGap_unscale (T : ℝ) (v : MasterTriple) (i : Fin 3)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) :
    criticalMasterGap T v i/meanSpacing T=occurrenceOrdinate (v i)-occurrenceOrdinate (v 2) := by sorry

theorem tripleAnchoredProfile_critical_quadratic_bound (R T : ℝ) (v : MasterTriple) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleAnchoredProfile v-criticalProfileApproximation (meanSpacing T)
      (criticalMasterGap T v 0) (criticalMasterGap T v 1)‖ ≤
      criticalProfileRemainderConstant R/(meanSpacing T)^4 := by sorry

theorem tripleAnchoredProfile_critical_leading_bound (R T : ℝ) (v : MasterTriple) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleAnchoredProfile v-kernelBenchmark‖ ≤
      criticalProfileLeadingConstant R/(meanSpacing T)^2 := by sorry

theorem tripleMasterKernel_critical_quadratic_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*
      criticalProfileApproximation (meanSpacing T) (criticalMasterGap T v 0) (criticalMasterGap T v 1)‖ ≤
      W*criticalProfileRemainderConstant R/(T*(meanSpacing T)^4)+16*Real.pi*M/(27*T^2) := by sorry

theorem tripleMasterKernel_critical_leading_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |criticalMasterGap T v 0|≤R) (hv : |criticalMasterGap T v 1|≤R) :
    ‖tripleMasterKernel ω T v-(ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*kernelBenchmark‖ ≤
      W*criticalProfileLeadingConstant R/(T*(meanSpacing T)^2)+16*Real.pi*M/(27*T^2) := by sorry

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
      W*criticalProfileRemainderConstant R/(T*(meanSpacing T)^4)+16*Real.pi*M/(27*T^2) := by sorry

theorem tripleTestKernel_critical_leading_bound (ω : ℝ → ℝ) (W M R T : ℝ)
    (hW : 0≤W) (hM : 0≤M) (hR : 0≤R) (hω : Differentiable ℝ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hw : ∀ x, |ω x|≤W) (hd : ∀ x, |deriv ω x|≤M)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (v : MasterTriple)
    (hline : ∀ i, occurrenceDisplacement (v i)=0)
    (hu : |meanSpacing T*actualProfileGap v 1|≤R) (hv : |meanSpacing T*actualProfileGap v 2|≤R) :
    ‖tripleMasterKernel ω T (tripleTestToMaster v)-(ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*kernelBenchmark‖ ≤
      W*criticalProfileLeadingConstant R/(T*(meanSpacing T)^2)+16*Real.pi*M/(27*T^2) := by sorry

theorem tripleAnchoredProfile_critical_repeated (i : ZeroOccurrence)
    (hi : occurrenceDisplacement i=0) :
    tripleAnchoredProfile (fun _ => i)=kernelBenchmark := by sorry

theorem tripleMasterKernel_critical_zero_weight (T : ℝ) (v : MasterTriple) (ℓ u w : ℝ) :
    tripleMasterKernel (fun _ => 0) T v-(0/T:ℝ)*criticalProfileApproximation ℓ u w=0 := by sorry

theorem zeroGapHorizontal_differences (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    |e-f|≤1 ∧ |e+g|≤1 ∧ |f+g|≤1 := by sorry

theorem zeroGapHorizontal_factor_bounds (h : ℝ) (hh : |h|≤1) :
    3≤4-h^2 ∧ 4-h^2≤4 := by sorry

theorem zeroGapHorizontal_factor_pos (h : ℝ) (hh : |h|≤1) : 0<4-h^2 := by sorry

theorem zeroGapHorizontal_factor_ne_zero (h : ℝ) (hh : |h|≤1) : 4-h^2≠0 := by sorry

theorem zeroGapHorizontalDenominator_bounds (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    27≤zeroGapHorizontalDenominator e f g ∧ zeroGapHorizontalDenominator e f g≤64 := by sorry

theorem zeroGapHorizontalDenominator_pos (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    0<zeroGapHorizontalDenominator e f g := by sorry

theorem zeroGapHorizontalDenominator_ne_zero (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    zeroGapHorizontalDenominator e f g≠0 := by sorry

theorem zeroGapHorizontal_numerator_lower (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    21≤24-(e-f)^2-(e+g)^2-(f+g)^2 := by sorry

theorem zeroGapHorizontalProfile_pos (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    0<zeroGapHorizontalProfile e f g := by sorry

theorem rationalProfile_zero_gap_horizontal (e f g : ℝ)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    rationalProfile 0 0 e f g=(zeroGapHorizontalProfile e f g:ℂ) := by sorry

theorem zeroGapHorizontalProfile_swap (e f g : ℝ) :
    zeroGapHorizontalProfile e f g=zeroGapHorizontalProfile f e g := by sorry

theorem zeroGapHorizontalProfile_reflection (e f g : ℝ) :
    zeroGapHorizontalProfile (-e) (-f) (-g)=zeroGapHorizontalProfile e f g := by sorry

theorem zeroGapHorizontalProfile_origin : zeroGapHorizontalProfile 0 0 0=3*Real.pi/8 := by sorry

theorem zeroGapHorizontalProfile_cancelling (d : ℝ) :
    zeroGapHorizontalProfile d d (-d)=3*Real.pi/8 := by sorry

theorem zeroGapHorizontalProfile_aligned (d : ℝ) (hd : |d|≤1/2) :
    zeroGapHorizontalProfile d d d=Real.pi*(3-d^2)/(8*(1-d^2)^2) := by sorry

theorem zeroGapHorizontalProfile_quarter :
    zeroGapHorizontalProfile (1/4) (1/4) (1/4)=94*Real.pi/225 := by sorry

theorem zeroGapHorizontalProfile_quarter_ne_origin :
    zeroGapHorizontalProfile (1/4) (1/4) (1/4)≠zeroGapHorizontalProfile 0 0 0 := by sorry

theorem zeroGapHorizontalProfile_corners (s t r : Bool) :
    zeroGapHorizontalProfile (if s then (1/2:ℝ) else -1/2)
      (if t then (1/2:ℝ) else -1/2) (if r then (1/2:ℝ) else -1/2) =
      if s=t ∧ t≠r then 3*Real.pi/8 else 11*Real.pi/18 := by sorry

theorem rationalProfile_zero_gap_scaled_bound (R ℓ u v e f g : ℝ) (hR : 0≤R) (hℓ : 1≤ℓ)
    (hu : |u|≤R) (hv : |v|≤R) (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/ℓ) (v/ℓ) e f g-(zeroGapHorizontalProfile e f g:ℂ)‖ ≤
      (16*Real.pi*R*(R+1)/9)/ℓ := by sorry

theorem rationalProfile_zero_gap_microscopic_bound (R T u v e f g : ℝ) (hR : 0≤R)
    (hT : 2*Real.pi*Real.exp (2*Real.pi)≤T) (hu : |u|≤R) (hv : |v|≤R)
    (he : |e|≤1/2) (hf : |f|≤1/2) (hg : |g|≤1/2) :
    ‖rationalProfile (u/meanSpacing T) (v/meanSpacing T) e f g-(zeroGapHorizontalProfile e f g:ℂ)‖ ≤
      (16*Real.pi*R*(R+1)/9)/meanSpacing T := by sorry

theorem rationalProfile_zero_gap_tendstoUniformlyOn (R : ℝ) (hR : 0≤R) :
    TendstoUniformlyOn
      (fun T (p : Fin 5 → ℝ) => rationalProfile (p 0/meanSpacing T) (p 1/meanSpacing T) (p 2) (p 3) (p 4))
      (fun p => (zeroGapHorizontalProfile (p 2) (p 3) (p 4):ℂ)) atTop (profileMicroscopicBox R) := by sorry

theorem criticalLocalNormalization_denominators (T : ℝ) (hT : 2*Real.pi<T) :
    0<T ∧ 0<Real.log T ∧ 0 < meanSpacing T := by sorry

theorem criticalLocalNormalization_identity (T : ℝ) (hT : 2*Real.pi<T) :
    (8/(T*Real.log T))*(3*Real.pi/8)=
      criticalLocalCoefficient T*(1/(T*meanSpacing T)) := by sorry

theorem criticalLocalNormalization_complex (T : ℝ) (hT : 2*Real.pi<T) :
    (8/((T:ℂ)*Real.log T))*kernelBenchmark=
      (criticalLocalCoefficient T:ℂ)*ordinateCoefficient T := by sorry

theorem criticalLocalCoefficient_transferRatio (T : ℝ) :
    (criticalLocalCoefficient T:ℂ)=(3/2:ℂ)*transferRatio T := by sorry

theorem criticalLocalNormalization_transferCoefficient (T : ℝ) :
    (8/((T:ℂ)*Real.log T))=(3/2:ℂ)*transferCoefficient T := by sorry

theorem criticalLocalCoefficient_sub_log (T : ℝ) (hT : 2*Real.pi<T) :
    criticalLocalCoefficient T=(3/2:ℝ)-3*Real.log (2*Real.pi)/(2*Real.log T) := by sorry

theorem criticalLocalCoefficient_bounds (T : ℝ) (hT : 2*Real.pi<T) :
    0<criticalLocalCoefficient T ∧ criticalLocalCoefficient T<(3/2:ℝ) := by sorry

theorem criticalLocalCoefficient_error (T : ℝ) (hT : 2*Real.pi<T) :
    |criticalLocalCoefficient T-(3/2:ℝ)|=3*Real.log (2*Real.pi)/(2*Real.log T) := by sorry

theorem criticalLocalCoefficient_tendsto :
    Tendsto criticalLocalCoefficient atTop (𝓝 (3/2:ℝ)) := by sorry

theorem criticalLocalCoefficient_complex_tendsto :
    Tendsto (fun T => (criticalLocalCoefficient T:ℂ)) atTop (𝓝 (3/2:ℂ)) := by sorry

theorem criticalLocalCoefficient_endpoint : criticalLocalCoefficient (2*Real.pi)=0 := by sorry

theorem criticalLocalNormalization_endpoint_spacing : meanSpacing (2*Real.pi)=0 := by sorry

theorem criticalLocalNormalization_endpoint_excluded :
    (8/((2*Real.pi)*Real.log (2*Real.pi)))*(3*Real.pi/8) ≠
      criticalLocalCoefficient (2*Real.pi)*(1/((2*Real.pi)*meanSpacing (2*Real.pi))) := by sorry

theorem tripleKernelLocalizationError_zero (T : ℝ) (v : MasterTriple) :
    tripleKernelLocalizationError (fun _ => 0) T v=0 := by sorry

theorem tripleAnchoredProfile_repeated (i : ZeroOccurrence) :
    tripleAnchoredProfile (fun _ => i) = rationalProfile 0 0
      (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by sorry

theorem tripleMasterKernel_localization_bound (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hd : ∀ x, |deriv ω x|≤M) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleMasterKernel ω T v-
      (ω (occurrenceOrdinate (v 2)/T)/T:ℝ)*tripleAnchoredProfile v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 0)-occurrenceOrdinate (v 1))^2)) := by sorry

theorem tripleTestKernel_localization_bound (ω : ℝ → ℝ) (M : ℝ)
    (hM : 0≤M) (hω : Differentiable ℝ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (hd : ∀ x, |deriv ω x|≤M) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleMasterKernel ω T (tripleTestToMaster v)-
      (ω (occurrenceOrdinate (v 0)/T)/T:ℝ)*actualRationalKernel v‖ ≤
      64*Real.pi*M/(27*T^2*(4+(occurrenceOrdinate (v 1)-occurrenceOrdinate (v 2))^2)) := by sorry

theorem tripleKernelLocalizationError_equal_ordinates (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple)
    (hg : occurrenceOrdinate (v 0)=occurrenceOrdinate (v 1)) :
    ‖tripleKernelLocalizationError ω T v‖ ≤ 16*Real.pi*(M:ℝ)/(27*T^2) := by sorry

end
end HigherCorrelations
