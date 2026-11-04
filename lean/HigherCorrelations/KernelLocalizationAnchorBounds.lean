import HigherCorrelations.KernelLocalizationMajorants

/-! UNCONDITIONAL near and far-center anchor sums, retaining multiplicity. -/
namespace HigherCorrelations
noncomputable section
open Set
open scoped NNReal

theorem localization_near_weight_zero (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 0<T)
    (ht : t ∉ Icc 0 (3*T)) (i : ZeroOccurrence) :
    localizationAnchorWeight .near ω T t i=0 := by
  classical
  by_cases hn : |t-occurrenceOrdinate i|≤T
  · have hc : t ∉ Icc T (2*T) := fun h => ht ⟨by linarith [h.1],by linarith [h.2]⟩
    have ha : occurrenceOrdinate i ∉ Icc T (2*T) := by
      intro h
      have hh := abs_le.mp hn
      exact ht ⟨by linarith [h.1,hh.1],by linarith [h.2,hh.2]⟩
    simp [localizationAnchorWeight,localizationRegionSet,hn,
      localization_weight_zero ω hs T t hT hc,localization_weight_zero ω hs T _ hT ha]
  · simp [localizationAnchorWeight,localizationRegionSet,hn]

theorem localization_near_anchor_sum :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) → ∀ s : Finset ZeroOccurrence,
      (∑ i ∈ s, localizationAnchorWeight .near ω T t i) ≤
        C*(M:ℝ)*Real.log (2*T+2)^2/T := by
  classical
  obtain ⟨C,hC,hb⟩ := localization_near_moment_finite
  refine ⟨C,hC,fun ω M hω T t hT ht s => ?_⟩
  let q := s.filter (fun i => |t-occurrenceOrdinate i|≤T)
  have hm := hb T t hT ht q (fun i hi => (Finset.mem_filter.mp hi).2)
  have he : (∑ i ∈ s, localizationAnchorWeight .near ω T t i) =
      ∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i)*|ω (t/T)-ω (occurrenceOrdinate i/T)| := by
    simp only [localizationAnchorWeight,localizationRegionSet,Set.indicator_apply,Set.mem_setOf_eq]
    exact (Finset.sum_filter _ _).symm
  rw [he]
  calc
    _ ≤ ∑ i ∈ q, ((M:ℝ)/T)*(|t-occurrenceOrdinate i| *ordinateKernel (t-occurrenceOrdinate i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hd := localization_weight_difference ω M hω T (occurrenceOrdinate i)
        (t-occurrenceOrdinate i) (by linarith)
      simp only [add_sub_cancel] at hd
      convert mul_le_mul_of_nonneg_left hd (ordinateKernel_nonneg (t-occurrenceOrdinate i)) using 1 <;> ring
    _ = ((M:ℝ)/T)*(∑ i ∈ q, |t-occurrenceOrdinate i| *ordinateKernel (t-occurrenceOrdinate i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((M:ℝ)/T)*(C*Real.log (2*T+2)^2) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem localization_far_center_anchor_sum :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ), 0≤M → (∀ x, |ω x|≤M) →
      ∀ T t : ℝ, 3≤T → t ∈ Icc T (2*T) → ∀ s : Finset ZeroOccurrence,
      (∑ i ∈ s, localizationAnchorWeight .farCenter ω T t i) ≤
        C*M*Real.log (2*T+2)/T := by
  classical
  obtain ⟨C,hC,hb⟩ := zeroKernelTail_summable_bound
  refine ⟨4*C,by positivity,fun ω M hM hw T t hT ht s => ?_⟩
  let q := s.filter (fun i => T< |t-occurrenceOrdinate i|)
  have hq := pairKernel_finite_le_restricted q (fun i => T≤|t-occurrenceOrdinate i|) t
    (fun i hi => (Finset.mem_filter.mp hi).2.le)
  change (∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i)) ≤ zeroKernelTail t T at hq
  have hh := (hb t T (by linarith)).2
  have hx : |(|t|+T)|≤4*T+2 := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  have hl := localization_local_log T (|t|+T) hT hx
  rw [abs_of_nonneg (by positivity : 0≤|t|+T)] at hl
  have hL := localization_log_ge_one T hT
  have he : (∑ i ∈ s, localizationAnchorWeight .farCenter ω T t i) =
      ∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i)*|ω (t/T)-ω (occurrenceOrdinate i/T)| := by
    simp only [localizationAnchorWeight,localizationRegionSet,Set.indicator_apply,Set.mem_setOf_eq,ht,and_true]
    exact (Finset.sum_filter _ _).symm
  rw [he]
  have hsum : (∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i)) ≤ 2*C*Real.log (2*T+2)/T := by
    apply (hq.trans hh).trans
    calc
      _ ≤ C*(2*Real.log (2*T+2))/(1+T) := by gcongr
      _ ≤ C*(2*Real.log (2*T+2))/T := div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i)*(2*M) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (ordinateKernel_nonneg _)
      exact (abs_sub _ _).trans (by linarith [hw (t/T),hw (occurrenceOrdinate i/T)])
    _ = (∑ i ∈ q, ordinateKernel (t-occurrenceOrdinate i))*(2*M) := (Finset.sum_mul _ _ _).symm
    _ ≤ (2*C*Real.log (2*T+2)/T)*(2*M) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

end
end HigherCorrelations
