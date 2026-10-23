import HigherCorrelations.TripleMasterIntegration

/-! UNCONDITIONAL exact full zero-series product and smoothed K_T identity.
Every ordered occurrence is retained, with its full horizontal displacement.
Parameters and the weight are fixed before any cutoff is removed. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- Finite rectangular products, before any infinite interchange. -/
theorem tripleMaster_finite_product (ω : ℝ → ℝ) (T X Y t : ℝ)
    (S : Fin 3 → Finset ZeroOccurrence) :
    (∑ v ∈ tripleDomain S, tripleMasterTerm ω T X Y v t) =
      (ω (t/T)/T : ℝ)*(∑ i ∈ S 0, pairZeroTerm i (X,t))*
        (∑ j ∈ S 1, pairZeroTerm j (Y,t))*
        star (∑ k ∈ S 2, pairZeroTerm k (X*Y,t)) := by
  classical
  let f : Fin 3 → ZeroOccurrence → ℂ :=
    ![fun i => pairZeroTerm i (X,t), fun i => pairZeroTerm i (Y,t),
      fun i => star (pairZeroTerm i (X*Y,t))]
  have hp := Finset.prod_univ_sum S f
  simp only [Fin.prod_univ_three] at hp
  have ht (v : MasterTriple) : tripleMasterTerm ω T X Y v t =
      (ω (t/T)/T : ℝ)*(f 0 (v 0)*f 1 (v 1)*f 2 (v 2)) := by
    simp [tripleMasterTerm, f, mul_assoc]
  simp_rw [ht]
  rw [← Finset.mul_sum, tripleDomain, ← hp]
  simp [f, mul_assoc]

/-- The infinite product is identified by absolutely convergent finite products. -/
theorem tripleMaster_product_eq (ω : ℝ → ℝ)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) (t : ℝ) :
    (∑' v : MasterTriple, tripleMasterTerm ω T X Y v t) =
      tripleMasterProduct ω T X Y t := by
  classical
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hlim := occurrence_cutoff_limit atTop
    (fun S : Finset ZeroOccurrence => tripleDomain (fun _ : Fin 3 => S))
    (fun v => eventually_atTop.mpr ⟨Finset.univ.image v, fun S hS => by
      rw [tripleDomain, Fintype.mem_piFinset]
      exact fun r => hS (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)⟩)
    (fun v => tripleMasterTerm ω T X Y v t)
    (tripleMaster_pointwise_summable ω hs T X Y hT hX hY t)
  have hx := (pairZeroTerm_summable X t hX).of_norm.hasSum
  have hy := (pairZeroTerm_summable Y t hY).of_norm.hasSum
  have hz := (pairZeroTerm_summable (X*Y) t hXY).of_norm.hasSum
  have hp := (((tendsto_const_nhds (x := ((ω (t/T)/T : ℝ) : ℂ))).mul hx).mul hy).mul
    (show Tendsto (fun S : Finset ZeroOccurrence => star (∑ k ∈ S, pairZeroTerm k (X*Y,t)))
      atTop (𝓝 (star (∑' k, pairZeroTerm k (X*Y,t)))) from
      continuous_star.continuousAt.tendsto.comp hz)
  simp_rw [tripleMaster_finite_product] at hlim
  exact tendsto_nhds_unique hlim hp

/-- Nonvanishing holds even when ordinates or occurrence indices coincide. -/
theorem tripleMasterDenominator_ne_zero (i : ZeroOccurrence) (t : ℝ) :
    tripleMasterDenominator i t ≠ 0 := by
  have h := pair_denominator_lower (t-occurrenceOrdinate i) (occurrenceDisplacement i)
    (pair_occurrence_displacement i)
  have : 0 < ‖tripleMasterDenominator i t‖ := by
    unfold tripleMasterDenominator
    nlinarith [sq_nonneg (t-occurrenceOrdinate i)]
  exact norm_pos_iff.mp this

/-- The t-dependent phases cancel exactly because the third base is XY. -/
theorem tripleMaster_phase_cancel (X Y t : ℝ) (hX : 0<X) (hY : 0<Y)
    (v : MasterTriple) :
    Complex.exp ((Real.log X : ℂ)*((occurrenceDisplacement (v 0):ℂ)+
      Complex.I*(occurrenceOrdinate (v 0)-t))) *
    Complex.exp ((Real.log Y : ℂ)*((occurrenceDisplacement (v 1):ℂ)+
      Complex.I*(occurrenceOrdinate (v 1)-t))) *
    star (Complex.exp ((Real.log (X*Y) : ℂ)*((occurrenceDisplacement (v 2):ℂ)+
      Complex.I*(occurrenceOrdinate (v 2)-t)))) = tripleMasterCoefficient X Y v := by
  simp only [tripleMasterCoefficient, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add,
    Real.log_mul hX.ne' hY.ne']
  congr 1
  apply Complex.ext <;>
    simp [occurrenceDisplacement, occurrenceOrdinate] <;> ring

/-- Termwise center-phase cancellation, including all three numerator factors 2. -/
theorem tripleMasterTerm_eq_kernel (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0<X) (hY : 0<Y) (v : MasterTriple) (t : ℝ) :
    tripleMasterTerm ω T X Y v t =
      (8*tripleMasterCoefficient X Y v)*tripleMasterKernelIntegrand ω T v t := by
  have hp := tripleMaster_phase_cancel X Y t hX hY v
  unfold tripleMasterTerm pairZeroTerm tripleMasterKernelIntegrand tripleMasterDenominator
  dsimp only
  simp only [star_div₀, star_mul, star_ofNat]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [← hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- K_T has the manuscript's literal outside factor 1/T. -/
theorem tripleMasterKernel_normalization (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel ω T v = (1/(T:ℂ)) * ∫ t : ℝ,
      (ω (t/T) : ℂ) / (tripleMasterDenominator (v 0) t *
        tripleMasterDenominator (v 1) t * star (tripleMasterDenominator (v 2) t)) := by
  unfold tripleMasterKernel tripleMasterKernelIntegrand
  rw [← integral_const_mul]
  congr 1
  funext t
  push_cast
  ring

theorem tripleMasterKernel_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T)
    (v : MasterTriple) : Integrable (tripleMasterKernelIntegrand ω T v) := by
  have he : tripleMasterKernelIntegrand ω T v =
      fun t => (1/8:ℂ)*tripleMasterTerm ω T 1 1 v t := by
    funext t
    rw [tripleMasterTerm_eq_kernel ω T 1 1 (by norm_num) (by norm_num)]
    simp [tripleMasterCoefficient]
  rw [he]
  exact (tripleMasterTerm_integrable ω hω hs T 1 1 hT le_rfl le_rfl v).const_mul _

theorem tripleMasterProduct_integrable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 0<T) (hX : 1≤X) (hY : 1≤Y) :
    Integrable (tripleMasterProduct ω T X Y) := by
  have hc (Z : ℝ) (hZ : 1≤Z) : Continuous (fun t : ℝ => pairZeroSeries (Z,t)) :=
    pairZeroSeries_continuous.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => hZ)
  have hXY : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have hcont : Continuous (tripleMasterProduct ω T X Y) := by
    unfold tripleMasterProduct
    exact (((Complex.continuous_ofReal.comp ((hω.comp (continuous_id.div_const T)).div_const T)).mul
      (hc _ hX)).mul (hc _ hY)).mul (hc _ hXY).star
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  apply tripleMaster_support ω hs T hT
  intro hz
  exact ht (by simp [tripleMasterProduct,hz])

theorem tripleMaster_integral_eq_kernel (ω : ℝ → ℝ) (T X Y : ℝ)
    (hX : 0<X) (hY : 0<Y) (v : MasterTriple) :
    (∫ t : ℝ, tripleMasterTerm ω T X Y v t) =
      8*(tripleMasterCoefficient X Y v * tripleMasterKernel ω T v) := by
  simp_rw [tripleMasterTerm_eq_kernel ω T X Y hX hY v]
  rw [integral_const_mul]
  exact mul_assoc _ _ _

/-- Absolute convergence of the explicit coefficient times K_T series. -/
theorem tripleMaster_kernel_norm_summable (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Summable (fun v : MasterTriple =>
      ‖tripleMasterCoefficient X Y v * tripleMasterKernel ω T v‖) := by
  have h := (tripleMaster_evaluated_norm_summable ω hω hs T X Y hT hX hY).div_const 8
  simp_rw [tripleMaster_integral_eq_kernel ω T X Y (by linarith) (by linarith),
    norm_mul, Complex.norm_ofNat] at h
  simpa using h

/-- Exact unconditional master identity; no distinctness restrictions are imposed. -/
theorem tripleMaster_kernel_identity (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    tripleMasterObservable ω T X Y = 8 * ∑' v : MasterTriple,
      tripleMasterCoefficient X Y v * tripleMasterKernel ω T v := by
  unfold tripleMasterObservable
  simp_rw [← tripleMaster_product_eq ω hs T X Y hT hX hY]
  rw [← tripleMaster_sum_integral ω hω hs T X Y hT hX hY]
  simp_rw [tripleMaster_integral_eq_kernel ω T X Y (by linarith) (by linarith)]
  exact tsum_mul_left

/-- Independent rectangular occurrence cutoffs converge to the named observable. -/
theorem tripleMasterObservable_independent_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun S : Fin 3 → Finset ZeroOccurrence =>
      ∫ t : ℝ, (ω (t/T)/T : ℝ)*(∑ i ∈ S 0, pairZeroTerm i (X,t))*
        (∑ j ∈ S 1, pairZeroTerm j (Y,t))*
        star (∑ k ∈ S 2, pairZeroTerm k (X*Y,t))) atTop
      (𝓝 (tripleMasterObservable ω T X Y)) := by
  have h := tripleMaster_independent_cutoff_limit ω hω hs T X Y hT hX hY
  simpa only [tripleMaster_finite_product,
    tripleMaster_product_eq ω hs T X Y hT hX hY, tripleMasterObservable] using h

/-- Inclusive |gamma| cutoffs, removed independently with the parameters fixed. -/
theorem tripleMasterObservable_height_cutoff (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T X Y : ℝ)
    (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    Tendsto (fun U : Fin 3 → ℝ =>
      ∫ t : ℝ, (ω (t/T)/T : ℝ)*(∑ i ∈ occurrenceCutoff (U 0), pairZeroTerm i (X,t))*
        (∑ j ∈ occurrenceCutoff (U 1), pairZeroTerm j (Y,t))*
        star (∑ k ∈ occurrenceCutoff (U 2), pairZeroTerm k (X*Y,t))) atTop
      (𝓝 (tripleMasterObservable ω T X Y)) := by
  have h := tripleMaster_height_cutoff_limit ω hω hs T X Y hT hX hY
  simpa only [tripleMaster_finite_product,
    tripleMaster_product_eq ω hs T X Y hT hX hY, tripleMasterObservable] using h

/-- Minimal height and base endpoints retain the factor eight. -/
theorem tripleMaster_kernel_minimal (ω : ℝ → ℝ) (hω : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) :
    tripleMasterObservable ω 3 1 1 = 8 * ∑' v : MasterTriple, tripleMasterKernel ω 3 v := by
  simpa [tripleMasterCoefficient] using
    tripleMaster_kernel_identity ω hω hs 3 1 1 (by norm_num) (by norm_num) (by norm_num)

theorem tripleMasterKernel_zero_weight (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel (fun _ => 0) T v = 0 := by
  simp [tripleMasterKernel, tripleMasterKernelIntegrand]

theorem tripleMasterKernel_neg_weight (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleMasterKernel (fun u => -ω u) T v = -tripleMasterKernel ω T v := by
  simp [tripleMasterKernel, tripleMasterKernelIntegrand, neg_div, integral_neg]

end
end HigherCorrelations
