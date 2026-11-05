import HigherCorrelations.FrozenProfileSummability

/-! UNCONDITIONAL summed localization and independent occurrence cutoffs.
T is fixed throughout: these cutoff limits are not height asymptotics. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem tripleFrozenTestProfile_summable_bound :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleFrozenTestProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenTestProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
  obtain ⟨A,B,hA,hB,h⟩ := tripleFrozenProfile_summable_bound
  refine ⟨A,B,hA,hB,fun ω M₀ M₁ hM₀ hw hω hs T hT => ?_⟩
  obtain ⟨hf,hb⟩ := h ω M₀ M₁ hM₀ hw hω hs T hT
  have he := tripleTestToMaster.tsum_eq (fun v => ‖tripleFrozenProfile ω T v‖)
  simp only [tripleFrozenProfile_test_order] at he
  refine ⟨?_,he.trans_le hb⟩
  simpa only [Function.comp_def,tripleFrozenProfile_test_order] using hf.comp_injective tripleTestToMaster.injective

theorem tripleFrozenProfile_sum_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, tripleMasterKernel ω T v) =
      (∑' v : MasterTriple, tripleFrozenProfile ω T v)+
      (∑' v : MasterTriple, tripleKernelLocalizationError ω T v) := by
  have hf := tripleFrozenProfile_norm_summable ω M₀ M₁ hM₀ hw hω hs T hT
  obtain ⟨C,hC,h⟩ := tripleKernelLocalizationError_summed_bound
  have he := (h ω M₀ M₁ hM₀ hw hω hs T hT).1
  simp_rw [tripleMasterKernel_localization ω hω.continuous hs T (by linarith)]
  exact hf.of_norm.tsum_add he.of_norm

theorem tripleFrozenTestProfile_sum_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)) =
      (∑' v : MasterTriple, tripleFrozenTestProfile ω T v)+
      (∑' v : MasterTriple, tripleKernelLocalizationError ω T (tripleTestToMaster v)) := by
  have he := tripleTestToMaster.tsum_eq (tripleFrozenProfile ω T)
  simp only [tripleFrozenProfile_test_order] at he
  rw [tripleTestToMaster.tsum_eq (tripleMasterKernel ω T),
    tripleTestToMaster.tsum_eq (tripleKernelLocalizationError ω T), he]
  exact tripleFrozenProfile_sum_identity ω M₀ M₁ hM₀ hw hω hs T hT

theorem tripleFrozenProfile_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, tripleFrozenProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenProfile ω T v)) :=
  triple_cutoff_limit _ (tripleFrozenProfile_norm_summable ω M₀ M₁ hM₀ hw hω hs T hT)

theorem tripleFrozenProfile_height_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), tripleFrozenProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenProfile ω T v)) := by
  apply occurrence_cutoff_limit atTop _ _ _
    (tripleFrozenProfile_norm_summable ω M₀ M₁ hM₀ hw hω hs T hT)
  intro v
  apply eventually_atTop.mpr
  refine ⟨fun r => |occurrenceOrdinate (v r)|,fun U hU => ?_⟩
  rw [tripleDomain,Fintype.mem_piFinset]
  exact fun r => (mem_occurrenceCutoff _ _).mpr (hU r)

theorem tripleFrozenTestProfile_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, tripleFrozenTestProfile ω T v)
      atTop (𝓝 (∑' v : MasterTriple, tripleFrozenTestProfile ω T v)) := by
  obtain ⟨A,B,hA,hB,h⟩ := tripleFrozenTestProfile_summable_bound
  exact triple_cutoff_limit _ (h ω M₀ M₁ hM₀ hw hω hs T hT).1

theorem tripleFrozenProfile_zero (T : ℝ) (v : MasterTriple) :
    tripleFrozenProfile (fun _ => 0) T v=0 := by simp [tripleFrozenProfile]

theorem tripleFrozenProfile_repeated (ω : ℝ → ℝ) (T : ℝ) (i : ZeroOccurrence) :
    tripleFrozenProfile ω T (fun _ => i) = (ω (occurrenceOrdinate i/T)/T:ℝ)*
      rationalProfile 0 0 (occurrenceDisplacement i) (occurrenceDisplacement i) (occurrenceDisplacement i) := by
  simp [tripleFrozenProfile,tripleAnchoredProfile]

end
end HigherCorrelations
