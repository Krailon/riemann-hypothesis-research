import HigherCorrelations.FrozenProfileDefinitions
import HigherCorrelations.KernelLocalizationSummed
import HigherCorrelations.TripleTestPhase

/-! UNCONDITIONAL absolute summability of the unweighted frozen profile.
No complex Fourier test or height limit enters these results. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem tripleFrozenProfile_test_order (ω : ℝ → ℝ) (T : ℝ) (v : MasterTriple) :
    tripleFrozenProfile ω T (tripleTestToMaster v)=tripleFrozenTestProfile ω T v := rfl

theorem tripleFrozenProfile_eq_sub (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    tripleFrozenProfile ω T v=tripleMasterKernel ω T v-tripleKernelLocalizationError ω T v := by
  rw [tripleMasterKernel_localization ω hw hs T hT v,add_sub_cancel_right]
  rfl

theorem tripleFrozenProfile_norm_le (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleFrozenProfile ω T v‖≤‖tripleMasterKernel ω T v‖+‖tripleKernelLocalizationError ω T v‖ := by
  rw [tripleFrozenProfile_eq_sub ω hw hs T hT v]
  exact norm_sub_le _ _

theorem tripleFrozen_weight_mass_bound (ω : ℝ → ℝ) (hw : Continuous ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (M : ℝ) (hM : 0≤M)
    (hb : ∀ u, |ω u|≤M) : (∫ u : ℝ, |ω u|)≤M := by
  have hi : Integrable (fun u : ℝ => |ω u|) :=
    (hw.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs)).norm
  have hj : Integrable ((Icc (1:ℝ) 2).indicator (fun _ : ℝ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hp (u : ℝ) : |ω u|≤(Icc (1:ℝ) 2).indicator (fun _ => M) u := by
    classical
    by_cases hu : u∈Icc (1:ℝ) 2
    · simpa only [Set.indicator_of_mem hu] using hb u
    · have hz : ω u=0 := by by_contra hn; exact hu (hs hn)
      simp [Set.indicator_of_notMem hu,hz]
  have hh := integral_mono hi hj hp
  simpa only [integral_indicator_const _ measurableSet_Icc,Real.volume_real_Icc,
    show max ((2:ℝ)-1) 0=1 by norm_num,one_smul] using hh

theorem tripleFrozen_kernel_mass_bound :
    ∃ A : ℝ, 0<A ∧ ∀ (ω : ℝ → ℝ), Continuous ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ M : ℝ, 0≤M → (∀ u, |ω u|≤M) → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleMasterKernel ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖)≤A*M*Real.log (2*T+2)^3 := by
  obtain ⟨C,hC,hQ,hbound⟩ := tripleMaster_uniform_integralNorm
  refine ⟨(8/3:ℝ)^3*C^3/8,by positivity,fun ω hw hs M hM hb T hT => ?_⟩
  have hk := tripleMaster_kernel_norm_summable ω hw hs T 1 1 hT le_rfl le_rfl
  simp only [tripleTest_coefficient_unit,one_mul] at hk
  refine ⟨hk,?_⟩
  have hi := hbound ω hw hs T 1 1 hT le_rfl le_rfl
  have he := tripleMaster_evaluated_norm_summable ω hw hs T 1 1 hT le_rfl le_rfl
  have hh := (he.tsum_le_tsum (fun v => norm_integral_le_integral_norm _) hi.1).trans hi.2
  simp only [tripleMaster_integral_eq_kernel ω T 1 1 (by norm_num) (by norm_num),
    tripleTest_coefficient_unit,one_mul,norm_mul,Complex.norm_ofNat,tsum_mul_left] at hh
  have hm := tripleFrozen_weight_mass_bound ω hw hs M hM hb
  have hL := localization_log_ge_one T hT
  have hh' : 8*(∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖)≤
      (8/3:ℝ)^3*C^3*Real.log (2*T+2)^3*M := by
    apply hh.trans
    unfold tripleMasterL1Bound
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hm
      (show 0≤(8/3:ℝ)^3*C^3*Real.log (2*T+2)^3 by positivity)
  nlinarith

theorem tripleFrozenProfile_summable_bound :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ u, |ω u|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
  obtain ⟨A,hA,ha⟩ := tripleFrozen_kernel_mass_bound
  obtain ⟨B,hB,hb⟩ := tripleKernelLocalizationError_summed_bound
  refine ⟨A,B,hA,hB,fun ω M₀ M₁ hM₀ hw hω hs T hT => ?_⟩
  obtain ⟨hk,bk⟩ := ha ω hω.continuous hs M₀ hM₀ hw T hT
  obtain ⟨he,be⟩ := hb ω M₀ M₁ hM₀ hw hω hs T hT
  have hp := tripleFrozenProfile_norm_le ω hω.continuous hs T (by linarith)
  have hf := (hk.add he).of_nonneg_of_le (fun v => norm_nonneg _) hp
  refine ⟨hf,?_⟩
  have h := hf.tsum_le_tsum hp (hk.add he)
  rw [hk.tsum_add he] at h
  exact h.trans (add_le_add bk be)

theorem tripleFrozenProfile_norm_summable (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) := by
  obtain ⟨A,B,hA,hB,h⟩ := tripleFrozenProfile_summable_bound
  exact (h ω M₀ M₁ hM₀ hw hω hs T hT).1

theorem tripleFrozenProfile_mass_triangle (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0)
    (hM₀ : 0≤M₀) (hw : ∀ u, |ω u|≤M₀) (hω : LipschitzWith M₁ ω)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T : ℝ) (hT : 3≤T) :
    (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
      (∑' v : MasterTriple, ‖tripleMasterKernel ω T v‖)+
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) := by
  obtain ⟨A,hA,ha⟩ := tripleFrozen_kernel_mass_bound
  obtain ⟨B,hB,hb⟩ := tripleKernelLocalizationError_summed_bound
  have hk := (ha ω hω.continuous hs M₀ hM₀ hw T hT).1
  have he := (hb ω M₀ M₁ hM₀ hw hω hs T hT).1
  have h := (tripleFrozenProfile_norm_summable ω M₀ M₁ hM₀ hw hω hs T hT).tsum_le_tsum
    (tripleFrozenProfile_norm_le ω hω.continuous hs T (by linarith)) (hk.add he)
  simpa only [hk.tsum_add he] using h

theorem tripleFrozenProfile_summable_bound_deriv :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ →
      (∀ u, |ω u|≤M₀) → Differentiable ℝ ω → (∀ u, |deriv ω u|≤M₁) →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleFrozenProfile ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleFrozenProfile ω T v‖) ≤
        A*M₀*Real.log (2*T+2)^3+B*(M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
  obtain ⟨A,B,hA,hB,h⟩ := tripleFrozenProfile_summable_bound
  refine ⟨A,B,hA,hB,fun ω M₀ M₁ hM₀ hM₁ hw hω hd hs T hT => ?_⟩
  apply h ω M₀ ⟨M₁,hM₁⟩ hM₀ hw _ hs T hT
  exact lipschitzWith_of_nnnorm_deriv_le hω (fun u => by
    change ‖deriv ω u‖≤M₁
    simpa only [Real.norm_eq_abs] using hd u)

end
end HigherCorrelations
