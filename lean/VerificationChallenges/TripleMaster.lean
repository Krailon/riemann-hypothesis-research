import HigherCorrelations.TripleMasterDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem tripleMasterTerm_continuous (ω : ℝ → ℝ) (hω : Continuous ω)
    (T X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) :
    Continuous (tripleMasterTerm ω T X Y v) := by sorry

theorem tripleMaster_support (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    Function.support (fun t : ℝ => ω (t/T)) ⊆ Icc T (2*T) := by sorry

theorem tripleMaster_weight_compact (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    HasCompactSupport (fun t : ℝ => ω (t/T)) := by sorry

theorem tripleMasterTerm_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) :
    Integrable (tripleMasterTerm ω T X Y v) := by sorry

theorem tripleMaster_weight_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ => |ω (t/T)|/T) := by sorry

theorem tripleMaster_weight_mass (ω : ℝ → ℝ) (T : ℝ) (hT : 0<T) :
    (∫ t : ℝ, |ω (t/T)|/T) = ∫ u : ℝ, |ω u| := by sorry

theorem tripleMasterMajorant_integrable (C₀ : ℝ) (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ) (hT : 0<T) :
    Integrable (tripleMasterMajorant C₀ ω T X Y) := by sorry

theorem tripleMasterMajorant_integral (C₀ : ℝ) (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T) :
    (∫ t : ℝ, tripleMasterMajorant C₀ ω T X Y t) = tripleMasterL1Bound C₀ ω T X Y := by sorry

theorem tripleMasterTerm_bound (ω : ℝ → ℝ) (T X Y : ℝ) (hT : 0<T)
    (hX : 1≤X) (hY : 1≤Y) (v : MasterTriple) (t : ℝ) :
    ‖tripleMasterTerm ω T X Y v t‖ ≤
      ((8/3 : ℝ)^3*X*Y*(|ω (t/T)|/T))*
        ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r)) := by sorry

theorem tripleMaster_finite_kernel (D : Finset MasterTriple) (t : ℝ) :
    (∑ v ∈ D, ∏ r : Fin 3, ordinateKernel (t-occurrenceOrdinate (v r))) ≤ (zeroKernelSum t)^3 := by sorry

theorem tripleMaster_finite_majorant (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y)
    (D : Finset MasterTriple) (t : ℝ) :
    (∑ v ∈ D, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterMajorant C₀ ω T X Y t := by sorry

theorem tripleMaster_finite_integralNorm_bound (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : Continuous ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (D : Finset MasterTriple) :
    (∑ v ∈ D, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by sorry

theorem tripleMaster_integralNorm_bound (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hQ : ∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2))
    (ω : ℝ → ℝ) (hω : Continuous ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ∧
    (∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by sorry

theorem tripleMaster_uniform_integralNorm :
    ∃ C₀ : ℝ, 0<C₀ ∧ (∀ t : ℝ, zeroKernelSum t ≤ C₀*Real.log (|t|+2)) ∧
      ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T X Y : ℝ, 3≤T → 1≤X → 1≤Y →
      Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ∧
      (∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) ≤ tripleMasterL1Bound C₀ ω T X Y := by sorry

theorem tripleMaster_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖) := by sorry

theorem tripleMaster_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    Summable (fun v : MasterTriple => ‖tripleMasterTerm ω T X Y v t‖) := by sorry

theorem tripleMaster_evaluated_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ‖∫ t : ℝ, tripleMasterTerm ω T X Y v t‖) := by sorry

theorem tripleMaster_sum_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t := by sorry

theorem tripleMaster_independent_cutoff_limit (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, ∑ v ∈ tripleDomain S, tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t)) := by sorry

theorem tripleMaster_height_cutoff_limit (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∫ t : ℝ, ∑ v ∈ tripleDomain (fun r => occurrenceCutoff (U r)),
        tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t)) := by sorry

theorem tripleMaster_zero_weight (T X Y : ℝ) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm (fun _ => 0) T X Y v t = 0 := by sorry

theorem tripleMaster_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm (fun u => -ω u) T X Y v t = -tripleMasterTerm ω T X Y v t := by sorry

theorem tripleMaster_minimal_parameters (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    Summable (fun v : MasterTriple => ∫ t : ℝ, ‖tripleMasterTerm ω 3 1 1 v t‖) ∧
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω 3 1 1 v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω 3 1 1 v t := by sorry

end
end HigherCorrelations
