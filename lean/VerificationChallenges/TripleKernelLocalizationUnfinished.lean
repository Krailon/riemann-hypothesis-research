import HigherCorrelations.KernelLocalizationDefinitions
import HigherCorrelations.KernelLocalizationSumDefinitions
import HigherCorrelations.FrozenProfileDefinitions
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
