import HigherCorrelations.KernelLocalizationSumDefinitions
import HigherCorrelations.KernelLocalizationBounds

/-! UNCONDITIONAL disjoint near/far partition, with exact endpoints and
integrability before splitting the complex error integral. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem localizationRegion_measurable (r : LocalizationRegion) (T c : ℝ) :
    MeasurableSet (localizationRegionSet r T c) := by
  cases r <;> unfold localizationRegionSet <;> measurability

theorem localizationRegion_disjoint (T c : ℝ) :
    Disjoint (localizationRegionSet .near T c) (localizationRegionSet .farCenter T c) ∧
    Disjoint (localizationRegionSet .near T c) (localizationRegionSet .farAnchor T c) ∧
    Disjoint (localizationRegionSet .farCenter T c) (localizationRegionSet .farAnchor T c) := by
  simp only [Set.disjoint_left, localizationRegionSet, Set.mem_setOf_eq]
  exact ⟨fun t h h' => (not_lt_of_ge h) h'.1,
    fun t h h' => (not_lt_of_ge h) h'.1, fun t h h' => h'.2.1 h.2⟩

theorem localization_weight_zero (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 0<T)
    (ht : t ∉ Icc T (2*T)) : ω (t/T)=0 := by
  by_contra h
  have hm := hs h
  apply ht
  exact ⟨(le_div_iff₀ hT).mp hm.1 |>.trans' (by simp), (div_le_iff₀ hT).mp hm.2⟩

theorem localizationErrorDensity_integrable (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (localizationErrorDensity ω T v) :=
  ((tripleKernelLocalizationIntegrand_integrable_lipschitz ω M hω T hT v).comp_sub_right
    (occurrenceOrdinate (v 2))).const_mul _

theorem localizationRegionalDensity_integrable (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    Integrable (localizationRegionalDensity r ω T v) :=
  (localizationErrorDensity_integrable ω M hω T hT v).indicator (localizationRegion_measurable r T _)

theorem localizationErrorDensity_integral (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    (∫ t : ℝ, localizationErrorDensity ω T v t) = tripleKernelLocalizationError ω T v := by
  simp only [localizationErrorDensity]
  rw [integral_const_mul, integral_sub_right_eq_self]
  rfl

theorem localizationRegionalDensity_partition (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T)
    (v : MasterTriple) (t : ℝ) :
    localizationErrorDensity ω T v t =
      localizationRegionalDensity .near ω T v t+
      localizationRegionalDensity .farCenter ω T v t+
      localizationRegionalDensity .farAnchor ω T v t := by
  classical
  unfold localizationRegionalDensity
  simp only [localizationRegionSet, Set.indicator_apply, Set.mem_setOf_eq]
  by_cases hn : |t-occurrenceOrdinate (v 2)| ≤ T
  · simp only [hn, not_lt_of_ge hn, false_and, ite_true, ite_false, add_zero]
  · have hf := lt_of_not_ge hn
    by_cases hc : t ∈ Icc T (2*T)
    · simp only [hn, hf, hc, not_true_eq_false, true_and, false_and, ite_true, ite_false, zero_add, add_zero]
    · by_cases ha : occurrenceOrdinate (v 2) ∈ Icc T (2*T)
      · simp only [hn, hf, hc, ha, not_false_eq_true, true_and, and_true, and_false,
          ite_true, ite_false, zero_add]
      · have ht0 := localization_weight_zero ω hs T t hT hc
        have ha0 := localization_weight_zero ω hs T _ hT ha
        simp only [hn, hf, hc, ha, not_false_eq_true, true_and, and_true, and_false,
          ite_true, ite_false, zero_add]
        simp [localizationErrorDensity, tripleKernelLocalizationIntegrand, ht0, ha0]


theorem localizationRegionalError_partition (ω : ℝ → ℝ) (M : ℝ≥0)
    (hω : LipschitzWith M ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleKernelLocalizationError ω T v = localizationRegionalError .near ω T v+
      localizationRegionalError .farCenter ω T v+localizationRegionalError .farAnchor ω T v := by
  rw [← localizationErrorDensity_integral]
  simp_rw [localizationRegionalDensity_partition ω hs T hT v]
  have hi := localizationRegionalDensity_integrable .near ω M hω T hT v
  have hj := localizationRegionalDensity_integrable .farCenter ω M hω T hT v
  have hk := localizationRegionalDensity_integrable .farAnchor ω M hω T hT v
  exact (integral_add (f := fun t => localizationRegionalDensity .near ω T v t+
    localizationRegionalDensity .farCenter ω T v t) (g := localizationRegionalDensity .farAnchor ω T v)
    (hi.add hj) hk).trans (congrArg (fun z => z+localizationRegionalError .farAnchor ω T v)
      (integral_add hi hj))


theorem localizationRegionalMass_nonneg (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (v : MasterTriple) : 0 ≤ localizationRegionalMass r ω T v :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem localizationRegionalError_norm_le (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (v : MasterTriple) :
    ‖localizationRegionalError r ω T v‖ ≤ localizationRegionalMass r ω T v :=
  norm_integral_le_integral_norm _

end
end HigherCorrelations
