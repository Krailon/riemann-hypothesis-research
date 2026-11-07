import HigherCorrelations.SmoothedTripleDefinitions
import HigherCorrelations.ProfileTransferLimits

/-! UNCONDITIONAL absolute convergence of the raw profile sum and independent cutoffs. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

theorem smoothedTripleTerm_frozen (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ)
    (hT : T ≠ 0) (v : MasterTriple) :
    smoothedTripleTerm ω φ T v = (T:ℂ)*
      (tripleFrozenTestProfile ω T v*complexFourier φ (tripleTestArguments T v)) := by
  unfold smoothedTripleTerm tripleFrozenTestProfile
  push_cast
  field_simp [hT]

theorem smoothedTripleTerm_summable (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Summable (fun v : MasterTriple => ‖smoothedTripleTerm ω φ T v‖) := by
  obtain ⟨M₀,M₁,hM₀,hw,hl⟩ := profileTransfer_smoothing_bounds ω hω
  have hf := tripleFrozenTestProfile_weighted_summable ω M₀ M₁ hM₀ hw hl
    (tripleBudgetWeight_support ω hω) φ hi κ T hT hs
  have ht : T≠0 := ne_of_gt (by linarith [Real.pi_pos])
  simp_rw [smoothedTripleTerm_frozen ω φ T ht,norm_mul]
  simpa only [norm_mul] using hf.mul_left ‖(T:ℂ)‖

theorem smoothedTripleTerm_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence => ∑ v ∈ tripleDomain S, smoothedTripleTerm ω φ T v)
      atTop (𝓝 (∑' v : MasterTriple, smoothedTripleTerm ω φ T v)) :=
  triple_cutoff_limit _ (smoothedTripleTerm_summable ω hω φ hi κ T hT hs)

theorem smoothedTripleTerm_height_cutoff (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (φ : ℝ × ℝ → ℂ) (hi : Integrable φ) (κ T : ℝ) (hT : 2*Real.pi<T)
    (hs : tsupport φ ⊆ signedMargin κ) :
    Tendsto (fun U : Fin 3 → ℝ => ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)), smoothedTripleTerm ω φ T v)
      atTop (𝓝 (∑' v : MasterTriple, smoothedTripleTerm ω φ T v)) := by
  apply occurrence_cutoff_limit atTop _ _ _ (smoothedTripleTerm_summable ω hω φ hi κ T hT hs)
  intro v
  apply eventually_atTop.mpr
  refine ⟨fun r => |occurrenceOrdinate (v r)|,fun U hU => ?_⟩
  rw [tripleDomain,Fintype.mem_piFinset]
  exact fun r => (mem_occurrenceCutoff _ _).mpr (hU r)

theorem smoothedTripleTerm_profile (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) (v : MasterTriple) :
    smoothedTripleTerm ω φ T v = (ω (occurrenceOrdinate (v 0)/T):ℂ)*
      rationalProfile (occurrenceOrdinate (v 1)-occurrenceOrdinate (v 0))
        (occurrenceOrdinate (v 2)-occurrenceOrdinate (v 0))
        (occurrenceDisplacement (v 1)) (occurrenceDisplacement (v 2)) (occurrenceDisplacement (v 0))*
      complexFourier φ (complexPair (actualGaps (meanSpacing T) v) (actualShifts (meanSpacing T) v)) := rfl

end
end HigherCorrelations
