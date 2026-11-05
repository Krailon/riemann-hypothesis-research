import HigherCorrelations.ComplexTestWeightedSummability
import HigherCorrelations.FrozenProfileLimits

/-! UNCONDITIONAL absolute complex-test weighting of the localized kernel.
All sums are ordered actual zero occurrences in test order. The factors 8 and
1/log T of the normalized statistic are not part of these summands.
Independent cutoffs tend to infinity only with T fixed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

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
        (A*M₀*Real.log (2*T+2)^3+C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T) := by
  obtain ⟨A,C,hA,hC,h⟩ := tripleFrozenTestProfile_summable_bound
  refine ⟨A,C,hA,hC,fun ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs => ?_⟩
  obtain ⟨hf,hb⟩ := h ω M₀ M₁ hM₀ hw hω hs T (tripleTestBase_bounds T hT).1
  exact signedTest_weighted_summable_bound _ hf _ hb φ hφ κ T hT hφs

theorem tripleTestKernel_weighted_bound :
    ∃ A : ℝ, 0<A ∧ ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ M : ℝ, 0≤M → (∀ u, |ω u|≤M) →
      ∀ (φ : ℝ × ℝ → ℂ), Integrable φ → ∀ κ T : ℝ, 2*Real.pi<T →
      tsupport φ ⊆ signedMargin κ →
      Summable (fun v : MasterTriple =>
        ‖tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ∧
      (∑' v : MasterTriple,
        ‖tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)‖) ≤
      tripleTestL1 φ*(tripleTestBase T)^(1-κ)*(A*M*Real.log (2*T+2)^3) := by
  obtain ⟨A,hA,h⟩ := tripleFrozen_kernel_mass_bound
  refine ⟨A,hA,fun ω hω hs M hM hw φ hφ κ T hT hφs => ?_⟩
  obtain ⟨hf,hb⟩ := h ω hω hs M hM hw T (tripleTestBase_bounds T hT).1
  have ht : Summable (fun v => ‖tripleMasterKernel ω T (tripleTestToMaster v)‖) :=
    hf.comp_injective tripleTestToMaster.injective
  have hm : (∑' v, ‖tripleMasterKernel ω T (tripleTestToMaster v)‖) ≤
      A*M*Real.log (2*T+2)^3 := by
    rw [tripleTestToMaster.tsum_eq (fun v => ‖tripleMasterKernel ω T v‖)]
    exact hb
  exact signedTest_weighted_summable_bound _ ht _ hm φ hφ κ T hT hφs

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
        (C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T) := by
  obtain ⟨C,hC,h⟩ := tripleKernelLocalizationError_summed_bound
  refine ⟨C,hC,fun ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs => ?_⟩
  obtain ⟨hf,hb⟩ := h ω M₀ M₁ hM₀ hw hω hs T (tripleTestBase_bounds T hT).1
  have ht : Summable (fun v => ‖tripleKernelLocalizationError ω T (tripleTestToMaster v)‖) :=
    hf.comp_injective tripleTestToMaster.injective
  have hm : (∑' v, ‖tripleKernelLocalizationError ω T (tripleTestToMaster v)‖) ≤
      C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
    rw [tripleTestToMaster.tsum_eq (fun v => ‖tripleKernelLocalizationError ω T v‖)]
    exact hb
  exact signedTest_weighted_summable_bound _ ht _ hm φ hφ κ T hT hφs

theorem tripleFrozenTestProfile_weighted_summable (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v : MasterTriple =>
      ‖tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)‖) := by
  obtain ⟨A,C,hA,hC,h⟩ := tripleFrozenTestProfile_weighted_bound
  exact (h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs).1

theorem tripleFrozenTestProfile_weighted_independent_cutoff
    (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0) (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀)
    (hω : LipschitzWith M₁ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S,
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (∑' v : MasterTriple,
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))) :=
  triple_cutoff_limit _
    (tripleFrozenTestProfile_weighted_summable ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs)

theorem tripleFrozenTestProfile_weighted_height_cutoff
    (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0) (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀)
    (hω : LipschitzWith M₁ ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) atTop
      (𝓝 (∑' v : MasterTriple,
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))) := by
  apply occurrence_cutoff_limit atTop _ _ _
    (tripleFrozenTestProfile_weighted_summable ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs)
  intro v
  apply eventually_atTop.mpr
  refine ⟨fun r => |occurrenceOrdinate (v r)|,fun U hU => ?_⟩
  rw [tripleDomain,Fintype.mem_piFinset]
  exact fun r => (mem_occurrenceCutoff _ _).mpr (hU r)

theorem tripleFrozenTestProfile_weighted_zero_test (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenTestProfile ω T v*complexFourier (fun _ => 0) (tripleTestArguments T v)=0 := by
  simp [complexFourier]

theorem tripleFrozenTestProfile_weighted_zero_weight (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenTestProfile (fun _ => 0) T v*complexFourier φ (tripleTestArguments T v)=0 := by
  simp [tripleFrozenTestProfile]

theorem tripleFrozenTestProfile_weighted_repeated (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ)
    (T : ℝ) (i : ZeroOccurrence) :
    tripleFrozenTestProfile ω T (fun _ => i)*complexFourier φ (tripleTestArguments T (fun _ => i)) =
      ((ω (occurrenceOrdinate i/T)/T:ℝ):ℂ)*
        rationalProfile 0 0 (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i)*
          complexFourier φ (tripleTestArguments T (fun _ => i)) := by
  rw [← tripleFrozenProfile_test_order]
  have he : tripleTestToMaster (fun _ => i)=(fun _ => i) := by
    funext r
    fin_cases r <;> rfl
  rw [he,tripleFrozenProfile_repeated]

end
end HigherCorrelations
