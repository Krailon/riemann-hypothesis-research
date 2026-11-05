import HigherCorrelations.ProfileTransferDefinitions
import HigherCorrelations.FrozenProfileWeighted
import HigherCorrelations.SignedTestAssembly

/-! UNCONDITIONAL normalized localization identity and independent cutoffs.
All occurrence cutoffs are removed at fixed T, before any height limit. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem frozenStatistic_profile_formula (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    frozenStatistic ω φ T = (8/((T:ℂ)*(Real.log T:ℂ)))*
      ∑' v : MasterTriple, (ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*
        complexFourier φ (tripleTestArguments T v) := by
  have hp (v : MasterTriple) :
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v) =
      (1/(T:ℂ))*((ω (occurrenceOrdinate (v 0)/T):ℂ)*actualRationalKernel v*
        complexFourier φ (tripleTestArguments T v)) := by
    simp only [tripleFrozenTestProfile,Complex.ofReal_div]
    ring
  unfold frozenStatistic
  simp_rw [hp]
  rw [tsum_mul_left]
  ring

theorem frozenStatistic_transfer_identity (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    signedStatistic ω φ T-frozenStatistic ω φ T=frozenTransferError ω φ T := by
  have hf := tripleFrozenTestProfile_weighted_summable ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs
  obtain ⟨C,hC,h⟩ := tripleLocalizationError_weighted_bound
  have he := (h ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs).1
  have ht : 0<T := by linarith [(tripleTestBase_bounds T hT).1]
  have hp (v : MasterTriple) : tripleMasterKernel ω T (tripleTestToMaster v)*
      complexFourier φ (tripleTestArguments T v) =
      tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)+
      tripleKernelLocalizationError ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v) := by
    rw [tripleTestKernel_localization ω hω.continuous hs T ht v]
    exact add_mul _ _ _
  rw [signed_zero_identity,frozenStatistic,frozenTransferError]
  simp_rw [hp]
  rw [hf.of_norm.tsum_add he.of_norm]
  ring

theorem frozenStatistic_independent_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => (8/(Real.log T:ℂ))*
      ∑ v ∈ tripleDomain S, tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))
      atTop (𝓝 (frozenStatistic ω φ T)) :=
  (tripleFrozenTestProfile_weighted_independent_cutoff ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs).const_mul _

theorem frozenStatistic_height_cutoff (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (φ : ℝ × ℝ → ℂ) (hφ : Integrable φ)
    (κ T : ℝ) (hT : 2*Real.pi<T) (hφs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => (8/(Real.log T:ℂ))*
      ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
        tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v))
      atTop (𝓝 (frozenStatistic ω φ T)) :=
  (tripleFrozenTestProfile_weighted_height_cutoff ω M₀ M₁ hM₀ hw hω hs φ hφ κ T hT hφs).const_mul _

theorem frozenStatistic_zero_test (ω : ℝ → ℝ) (T : ℝ) :
    frozenStatistic ω (fun _ => 0) T=0 := by
  simp [frozenStatistic,tripleFrozenTestProfile_weighted_zero_test]

theorem frozenStatistic_zero_weight (φ : ℝ × ℝ → ℂ) (T : ℝ) :
    frozenStatistic (fun _ => 0) φ T=0 := by
  simp [frozenStatistic,tripleFrozenTestProfile_weighted_zero_weight]

end
end HigherCorrelations
