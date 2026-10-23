import HigherCorrelations.TripleExpansionDefinitions
import HigherCorrelations.TripleMasterPatternDefinitions

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

theorem tripleMaster_finite_product (ω : ℝ → ℝ) (T X Y t : ℝ)
    (S : Fin 3 → Finset ZeroOccurrence) :
    (∑ v ∈ tripleDomain S, tripleMasterTerm ω T X Y v t) =
      (ω (t/T)/T : ℝ)*(∑ i ∈ S 0, pairZeroTerm i (X,t))*
        (∑ j ∈ S 1, pairZeroTerm j (Y,t))*
        star (∑ k ∈ S 2, pairZeroTerm k (X*Y,t)) := by sorry

theorem tripleMaster_product_eq (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    (∑' v : MasterTriple, tripleMasterTerm ω T X Y v t) =
      tripleMasterProduct ω T X Y t := by sorry

theorem tripleMasterDenominator_ne_zero (i : ZeroOccurrence) (t : ℝ) :
    tripleMasterDenominator i t ≠ 0 := by sorry

theorem tripleMaster_phase_cancel (X Y t : ℝ) (hX : 0<X) (hY : 0<Y)
    (v : MasterTriple) :
    Complex.exp ((Real.log X : ℂ)*((occurrenceDisplacement (v 0):ℂ)+
      Complex.I*(occurrenceOrdinate (v 0)-t))) *
    Complex.exp ((Real.log Y : ℂ)*((occurrenceDisplacement (v 1):ℂ)+
      Complex.I*(occurrenceOrdinate (v 1)-t))) *
    star (Complex.exp ((Real.log (X*Y) : ℂ)*((occurrenceDisplacement (v 2):ℂ)+
      Complex.I*(occurrenceOrdinate (v 2)-t)))) = tripleMasterCoefficient X Y v := by sorry

theorem tripleMasterTerm_eq_kernel (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0<X) (hY : 0<Y) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm ω T X Y v t =
      (8*tripleMasterCoefficient X Y v)*tripleMasterKernelIntegrand ω T v t := by sorry

theorem tripleMasterKernel_normalization (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel ω T v = (1/(T:ℂ)) * ∫ t : ℝ,
      (ω (t/T) : ℂ) / (tripleMasterDenominator (v 0) t *
        tripleMasterDenominator (v 1) t * star (tripleMasterDenominator (v 2) t)) := by sorry

theorem tripleMasterKernel_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T)
    (v : MasterTriple) : Integrable (tripleMasterKernelIntegrand ω T v) := by sorry

theorem tripleMasterProduct_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) :
    Integrable (tripleMasterProduct ω T X Y) := by sorry

theorem tripleMaster_integral_eq_kernel (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0<X) (hY : 0<Y) (v : MasterTriple) :
    (∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      8*(tripleMasterCoefficient X Y v * tripleMasterKernel ω T v) := by sorry

theorem tripleMaster_kernel_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple =>
      ‖tripleMasterCoefficient X Y v * tripleMasterKernel ω T v‖) := by sorry

theorem tripleMaster_kernel_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = 8 * ∑' v : MasterTriple,
      tripleMasterCoefficient X Y v * tripleMasterKernel ω T v := by sorry

theorem tripleMasterObservable_independent_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, (ω (t/T)/T : ℝ)*(∑ i ∈ S 0, pairZeroTerm i (X,t))*
        (∑ j ∈ S 1, pairZeroTerm j (Y,t))*
        star (∑ k ∈ S 2, pairZeroTerm k (X*Y,t))) atTop
      (𝓝 (tripleMasterObservable ω T X Y)) := by sorry

theorem tripleMasterObservable_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∫ t : ℝ, (ω (t/T)/T : ℝ)*(∑ i ∈ occurrenceCutoff (U 0), pairZeroTerm i (X,t))*
        (∑ j ∈ occurrenceCutoff (U 1), pairZeroTerm j (Y,t))*
        star (∑ k ∈ occurrenceCutoff (U 2), pairZeroTerm k (X*Y,t))) atTop
      (𝓝 (tripleMasterObservable ω T X Y)) := by sorry

theorem tripleMaster_kernel_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleMasterObservable ω 3 1 1 = 8 * ∑' v : MasterTriple, tripleMasterKernel ω 3 v := by sorry

theorem tripleMasterKernel_zero_weight (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel (fun _ => 0) T v = 0 := by sorry

theorem tripleMasterKernel_neg_weight (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel (fun u => -ω u) T v = -tripleMasterKernel ω T v := by sorry

theorem tripleMasterPattern_allEqual (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .allEqual =
      ∑' i : ZeroOccurrence, tripleMasterKernelTerm ω T X Y ![i,i,i] := by sorry

theorem tripleMasterPattern_only01 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only01 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2] := by sorry

theorem tripleMasterPattern_only02 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only02 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1] := by sorry

theorem tripleMasterPattern_only12 (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .only12 =
      ∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2] := by sorry

theorem tripleMasterPattern_allDistinct (ω : ℝ → ℝ) (T X Y : ℝ) :
    tripleMasterPatternSeries ω T X Y .allDistinct =
      ∑' v : MasterDistinctTriple, tripleMasterKernelTerm ω T X Y v.val := by sorry

theorem tripleMasterKernelTerm_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple => ‖tripleMasterKernelTerm ω T X Y v‖) := by sorry

theorem tripleMasterPattern_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Summable (fun v : MasterPatternTriple p => ‖tripleMasterKernelTerm ω T X Y v.val‖) := by sorry

theorem tripleMasterPattern_integralNorm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Summable (fun v : MasterPatternTriple p => ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v.val t‖) := by sorry

theorem tripleMasterPattern_integralNorm_le (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    (∑' v : MasterPatternTriple p, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v.val t‖) ≤
      ∑' v : MasterTriple, ∫ t : ℝ, ‖tripleMasterTerm ω T X Y v t‖ := by sorry

theorem tripleMasterPattern_integral_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    tripleMasterPatternSeries ω T X Y p =
      ∫ t : ℝ, ∑' v : MasterPatternTriple p, tripleMasterTerm ω T X Y v.val t := by sorry

theorem tripleMaster_pattern_decomposition (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = ∑ p : TriplePattern, tripleMasterPatternSeries ω T X Y p := by sorry

theorem tripleMaster_rows_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun i : ZeroOccurrence => ‖tripleMasterKernelTerm ω T X Y ![i,i,i]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1]‖) ∧
    Summable (fun q : MasterUnequalPair => ‖tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2]‖) ∧
    Summable (fun v : MasterDistinctTriple => ‖tripleMasterKernelTerm ω T X Y v.val‖) := by sorry

theorem tripleMaster_five_subseries (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (∑' i : ZeroOccurrence, tripleMasterKernelTerm ω T X Y ![i,i,i]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.1,q.val.2]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.1]) +
      (∑' q : MasterUnequalPair, tripleMasterKernelTerm ω T X Y ![q.val.1,q.val.2,q.val.2]) +
      (∑' v : MasterDistinctTriple, tripleMasterKernelTerm ω T X Y v.val) := by sorry

theorem tripleMasterPattern_pointwise_summable (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) (t : ℝ) :
    Summable (fun v : MasterPatternTriple p => ‖tripleMasterTerm ω T X Y v.val t‖) := by sorry

theorem tripleMasterPattern_finite_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y)
    (S : Fin 3 → Finset ZeroOccurrence) (p : TriplePattern) :
    (∫ t : ℝ, ∑ v ∈ patternDomain id S p, tripleMasterTerm ω T X Y v t) =
      ∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v := by sorry

theorem tripleMasterPattern_independent_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by sorry

theorem tripleMasterPattern_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∑ v ∈ patternDomain id (fun r => occurrenceCutoff (U r)) p,
        tripleMasterKernelTerm ω T X Y v) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by sorry

theorem tripleMasterPattern_integral_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, ∑ v ∈ patternDomain id S p, tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by sorry

theorem tripleMasterPattern_integral_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (p : TriplePattern) :
    Tendsto (fun U : Fin 3 → ℝ => ∫ t : ℝ,
      ∑ v ∈ patternDomain id (fun r => occurrenceCutoff (U r)) p,
        tripleMasterTerm ω T X Y v t) atTop
      (𝓝 (tripleMasterPatternSeries ω T X Y p)) := by sorry

theorem tripleMasterPattern_minimal (ω : ℝ → ℝ) (p : TriplePattern) :
    tripleMasterPatternSeries ω 3 1 1 p =
      8 * ∑' v : MasterPatternTriple p, tripleMasterKernel ω 3 v.val := by sorry

theorem tripleMasterPattern_empty_slot (ω : ℝ → ℝ) (T X Y : ℝ)
    (S : Fin 3 → Finset ZeroOccurrence) (r : Fin 3) (hS : S r = ∅) (p : TriplePattern) :
    (∑ v ∈ patternDomain id S p, tripleMasterKernelTerm ω T X Y v) = 0 := by sorry

theorem tripleWordSign_product (w : MasterWord) :
    tripleWordSign w = ∏ r : Fin 3, (if w r = .P then (-1:ℤ) else 1) := by sorry

theorem tripleComponent_remainder (X t : ℝ) :
    tripleComponent .H X t = pairArchError (X,t)+pairDSError (X,t)+
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by sorry

theorem tripleComponent_explicit_formula (X t : ℝ) (hX : 1≤X) :
    pairZeroSeries (X,t) = -tripleComponent .P X t + tripleComponent .A X t +
      tripleComponent .H X t := by sorry

theorem tripleComponent_continuous (l : MasterLetter) (X : ℝ) (hX : 1≤X) :
    Continuous (tripleComponent l X) := by sorry

theorem tripleSmoothedIntegral_normalization (ω : ℝ → ℝ) (T : ℝ) (f g h : ℝ → ℂ) :
    tripleSmoothedIntegral ω T f g h = (1/(T:ℂ))*
      ∫ t : ℝ, (ω (t/T):ℂ)*f t*g t*star (h t) := by sorry

theorem tripleWordIntegrand_continuous (ω : ℝ → ℝ) (hω : Continuous ω)
    (T X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord) :
    Continuous (tripleWordIntegrand ω T X Y w) := by sorry

theorem tripleWordIntegrand_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) (w : MasterWord) :
    Integrable (tripleWordIntegrand ω T X Y w) := by sorry

theorem tripleWord_algebra (F : Fin 3 → MasterLetter → ℂ) :
    (-F 0 .P+F 0 .A+F 0 .H)*(-F 1 .P+F 1 .A+F 1 .H)*
      star (-F 2 .P+F 2 .A+F 2 .H) =
    ∑ w : MasterWord, (tripleWordSign w:ℂ)*
      (F 0 (w 0)*F 1 (w 1)*star (F 2 (w 2))) := by sorry

theorem tripleMasterProduct_word_expansion (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    tripleMasterProduct ω T X Y t =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegrand ω T X Y w t := by sorry

theorem tripleMaster_word_expansion (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w := by sorry

theorem tripleWordTable_nodup : (tripleWordTable.map Prod.fst).Nodup := by sorry

theorem tripleWordTable_complete : (tripleWordTable.map Prod.fst).toFinset =
    (Finset.univ : Finset MasterWord) := by sorry

theorem tripleWordTable_correct : ∀ row ∈ tripleWordTable,
    row.2.1 = tripleWordSign row.1 ∧ row.2.2 = tripleWordHasH row.1 := by sorry

theorem tripleWord_counts : Fintype.card MasterWord = 27 ∧
    (Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = false)).card = 8 ∧
    (Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = true)).card = 19 := by sorry

theorem tripleMaster_table_expansion (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (tripleWordTable.map (fun row => (row.2.1:ℂ)*tripleWordIntegral ω T X Y row.1)).sum := by sorry

theorem tripleMaster_word_split (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y =
      (∑ w ∈ Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = false),
        (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w) +
      (∑ w ∈ Finset.univ.filter (fun w : MasterWord => tripleWordHasH w = true),
        (tripleWordSign w:ℂ)*tripleWordIntegral ω T X Y w) := by sorry

theorem tripleMaster_word_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleMasterObservable ω 3 1 1 =
      ∑ w : MasterWord, (tripleWordSign w:ℂ)*tripleWordIntegral ω 3 1 1 w := by sorry

theorem tripleWordIntegral_zero_weight (T X Y : ℝ) (w : MasterWord) :
    tripleWordIntegral (fun _ => 0) T X Y w = 0 := by sorry

theorem tripleWordIntegral_neg_weight (ω : ℝ → ℝ) (T X Y : ℝ) (w : MasterWord) :
    tripleWordIntegral (fun t => -ω t) T X Y w = -tripleWordIntegral ω T X Y w := by sorry

end
end HigherCorrelations
