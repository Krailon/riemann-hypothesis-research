import HigherCorrelations.SignedMasterBounds

/-! UNCONDITIONAL master identity for all positive bases. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

theorem tripleMaster_positive_product_eq (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) (t : ℝ) :
    (∑' v : MasterTriple, tripleMasterTerm ω T X Y v t) =
      tripleMasterProduct ω T X Y t := by
  classical
  have hlim := occurrence_cutoff_limit atTop
    (fun S : Finset ZeroOccurrence => tripleDomain (fun _ : Fin 3 => S))
    (fun v => eventually_atTop.mpr ⟨Finset.univ.image v, fun S hS => by
      rw [tripleDomain, Fintype.mem_piFinset]
      exact fun r => hS (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩)
    (fun v => tripleMasterTerm ω T X Y v t)
    (tripleMaster_positive_pointwise_summable ω hs T X Y hT hX hY t)
  have hx := (pairZeroTerm_positive_summable X t).of_norm.hasSum
  have hy := (pairZeroTerm_positive_summable Y t).of_norm.hasSum
  have hz := (pairZeroTerm_positive_summable (X*Y) t).of_norm.hasSum
  have hp := (((tendsto_const_nhds (x := ((ω (t/T)/T : ℝ) : ℂ))).mul hx).mul hy).mul
    (show Tendsto (fun S : Finset ZeroOccurrence => star (∑ k ∈ S, pairZeroTerm k (X*Y,t)))
      atTop (𝓝 (star (∑' k, pairZeroTerm k (X*Y,t)))) from
      continuous_star.continuousAt.tendsto.comp hz)
  simp_rw [tripleMaster_finite_product] at hlim
  exact tendsto_nhds_unique hlim hp

theorem tripleMaster_positive_sum_integral (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    (∑' v : MasterTriple, ∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      ∫ t : ℝ, ∑' v : MasterTriple, tripleMasterTerm ω T X Y v t :=
  integral_occurrence_sum volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_positive_integrable ω hω hs T X Y (by linarith) hX hY)
    (tripleMaster_positive_integralNorm_summable ω hω hs T X Y hT hX hY)

theorem tripleMaster_positive_kernel_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    tripleMasterObservable ω T X Y = 8 * ∑' v : MasterTriple,
      tripleMasterCoefficient X Y v * tripleMasterKernel ω T v := by
  unfold tripleMasterObservable
  simp_rw [← tripleMaster_positive_product_eq ω hs T X Y hT hX hY]
  rw [← tripleMaster_positive_sum_integral ω hω hs T X Y hT hX hY]
  simp_rw [tripleMaster_integral_eq_kernel ω T X Y (by linarith) (by linarith)]
  exact tsum_mul_left


theorem tripleMaster_positive_kernel_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    Summable (fun v : MasterTriple => ‖tripleMasterCoefficient X Y v*tripleMasterKernel ω T v‖) := by
  have h := (evaluated_integrals_summable volume (tripleMasterTerm ω T X Y)
    (tripleMasterTerm_positive_integrable ω hω hs T X Y (by linarith) hX hY) _
    (tripleMaster_positive_integralNorm_summable ω hω hs T X Y hT hX hY)
    (fun v => norm_integral_le_integral_norm _)).div_const 8
  simp_rw [tripleMaster_integral_eq_kernel ω T X Y hX hY,norm_mul,Complex.norm_ofNat] at h
  simpa using h

theorem tripleMaster_positive_kernel_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 0<X) (hY : 0<Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      8*∑ v ∈ tripleDomain S, tripleMasterCoefficient X Y v*tripleMasterKernel ω T v)
      atTop (𝓝 (tripleMasterObservable ω T X Y)) := by
  rw [tripleMaster_positive_kernel_identity ω hω hs T X Y hT hX hY]
  exact (triple_cutoff_limit _ (tripleMaster_positive_kernel_summable ω hω hs T X Y hT hX hY)).const_mul _

end
end HigherCorrelations
