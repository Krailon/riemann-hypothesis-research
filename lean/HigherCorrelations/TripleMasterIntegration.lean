import HigherCorrelations.TripleMasterBounds

/-! UNCONDITIONAL sum-integral interchange, now with the actual integral-norm
hypothesis discharged. Heights and smoothing are fixed before removing cutoffs. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem tripleMaster_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) := by
  obtain ⟨C,hC,hQ,h⟩ := tripleMaster_uniform_integralNorm
  exact (h ω hω hs T X Y hT hX hY).1

theorem tripleMaster_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    Summable (fun v : MasterTriple => ‖tripleMasterTerm ω T X Y v t‖) := by
  obtain ⟨C,hC,hQ⟩ := zeroKernel_summable_bound
  exact summable_of_sum_le (fun v => norm_nonneg _)
    (fun D => tripleMaster_finite_majorant C hC.le (fun u => (hQ u).2) ω hs T X Y hT hX hY D t)

theorem tripleMaster_evaluated_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ‖∫ t : ℝ, tripleMasterTerm ω T X Y v t‖) :=
  evaluated_integrals_summable volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY) _
    (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY)
    (fun v => norm_integral_le_integral_norm _)

theorem tripleMaster_sum_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t :=
  integral_occurrence_sum volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY)
    (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY)

theorem tripleMaster_independent_cutoff_limit (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, ∑ v ∈ tripleDomain S, tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t)) := by
  classical
  apply integral_occurrence_cutoff_limit volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY)
    (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY)
  intro v
  apply eventually_atTop.mpr
  refine ⟨fun r => {v r},fun S hS => ?_⟩
  rw [tripleDomain,Fintype.mem_piFinset]
  exact fun r => hS r (Finset.mem_singleton_self _)

theorem tripleMaster_height_cutoff_limit (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∫ t : ℝ, ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
        tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t)) := by
  apply integral_occurrence_cutoff_limit volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_integrable ω hω hs T X Y (by linarith) hX hY)
    (tripleMaster_integralNorm_summable ω hω hs T X Y hT hX hY)
  intro v
  apply eventually_atTop.mpr
  refine ⟨fun r => |occurrenceOrdinate (v r)|,fun U hU => ?_⟩
  rw [tripleDomain,Fintype.mem_piFinset]
  exact fun r => (mem_occurrenceCutoff _ _).mpr (hU r)

theorem tripleMaster_zero_weight (T X Y : ℝ) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm (fun _ => 0) T X Y v t = 0 := by simp [tripleMasterTerm]

theorem tripleMaster_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm (fun u => -ω u) T X Y v t = -tripleMasterTerm ω T X Y v t := by
  simp [tripleMasterTerm]
  ring

theorem tripleMaster_minimal_parameters (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω 3 1 1 v t‖) ∧
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω 3 1 1 v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω 3 1 1 v t :=
  ⟨tripleMaster_integralNorm_summable ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num),
   tripleMaster_sum_integral ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)⟩

end
end HigherCorrelations
