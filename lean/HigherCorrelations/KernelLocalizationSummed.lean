import HigherCorrelations.KernelLocalizationFarAnchor

/-! UNCONDITIONAL summed localization. Finite integral-norm estimates imply
absolute summability before any complex sum/integral interchange is invoked. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem localizationRegionalMass_summable_of_finite (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T B : ℝ) (hb : ∀ D : Finset MasterTriple, (∑ v ∈ D, localizationRegionalMass r ω T v)≤B) :
    Summable (localizationRegionalMass r ω T) ∧ (∑' v, localizationRegionalMass r ω T v)≤B :=
  ⟨summable_of_sum_le (localizationRegionalMass_nonneg r ω T) hb,
    Real.tsum_le_of_sum_le (localizationRegionalMass_nonneg r ω T) hb⟩

theorem localizationRegionalError_summable_bound (r : LocalizationRegion) (ω : ℝ → ℝ)
    (T : ℝ) (hm : Summable (localizationRegionalMass r ω T)) :
    Summable (fun v => ‖localizationRegionalError r ω T v‖) ∧
      (∑' v, ‖localizationRegionalError r ω T v‖) ≤ ∑' v, localizationRegionalMass r ω T v := by
  have h := hm.of_nonneg_of_le (fun v => norm_nonneg _) (localizationRegionalError_norm_le r ω T)
  exact ⟨h,h.tsum_le_tsum (localizationRegionalError_norm_le r ω T) hm⟩

theorem localizationRegional_sum_integral (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T)
    (hm : Summable (localizationRegionalMass r ω T)) :
    (∑' v, localizationRegionalError r ω T v) = ∫ t : ℝ, ∑' v, localizationRegionalDensity r ω T v t :=
  integral_tsum_of_summable_integral_norm
    (localizationRegionalDensity_integrable r ω M hω T hT) hm

theorem localization_near_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (localizationRegionalMass .near ω T) ∧
      (∑' v, localizationRegionalMass .near ω T v) ≤ C*(M:ℝ)*Real.log (2*T+2)^4/T := by
  obtain ⟨C,hC,hb⟩ := localization_near_finite_mass
  exact ⟨C,hC,fun ω M hw hs T hT => localizationRegionalMass_summable_of_finite .near ω T _ (hb ω M hw hs T hT)⟩

theorem localization_far_center_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → ∀ T : ℝ, 3≤T →
      Summable (localizationRegionalMass .farCenter ω T) ∧
      (∑' v, localizationRegionalMass .farCenter ω T v) ≤ C*M₀*Real.log (2*T+2)^3/T := by
  obtain ⟨C,hC,hb⟩ := localization_far_center_finite_mass
  exact ⟨C,hC,fun ω M₀ M₁ hM₀ hw hω T hT => localizationRegionalMass_summable_of_finite .farCenter ω T _ (hb ω M₀ M₁ hM₀ hw hω T hT)⟩

theorem localization_far_anchor_summed_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (localizationRegionalMass .farAnchor ω T) ∧
      (∑' v, localizationRegionalMass .farAnchor ω T v) ≤ C*M₀*Real.log (2*T+2)^3/T := by
  obtain ⟨C,hC,hb⟩ := localization_far_anchor_finite_mass
  exact ⟨C,hC,fun ω M₀ M₁ hM₀ hw hω hs T hT => localizationRegionalMass_summable_of_finite .farAnchor ω T _ (hb ω M₀ M₁ hM₀ hw hω hs T hT)⟩

theorem localization_total_error_le_masses (ω : ℝ → ℝ) (M : ℝ≥0)
    (hw : LipschitzWith M ω) (hs : Function.support ω ⊆ Icc (1:ℝ) 2)
    (T : ℝ) (hT : 0<T) (v : MasterTriple) :
    ‖tripleKernelLocalizationError ω T v‖ ≤ localizationRegionalMass .near ω T v+
      localizationRegionalMass .farCenter ω T v+localizationRegionalMass .farAnchor ω T v := by
  rw [localizationRegionalError_partition ω M hw hs T hT v]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (localizationRegionalError_norm_le .near ω T v)
      (localizationRegionalError_norm_le .farCenter ω T v)))
    (localizationRegionalError_norm_le .farAnchor ω T v))

theorem tripleKernelLocalizationError_summed_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → Summable (fun v : MasterTriple => ‖tripleKernelLocalizationError ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) ≤
        C*((M₁:ℝ)*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
  obtain ⟨A,hA,ha⟩ := localization_near_summed_mass
  obtain ⟨B,hB,hb⟩ := localization_far_center_summed_mass
  obtain ⟨C,hC,hc⟩ := localization_far_anchor_summed_mass
  refine ⟨A+B+C,by positivity,fun ω M₀ M₁ hM₀ hw hω hs T hT => ?_⟩
  obtain ⟨hn,bn⟩ := ha ω M₁ hω hs T hT
  obtain ⟨hf,bf⟩ := hb ω M₀ M₁ hM₀ hw hω T hT
  obtain ⟨hg,bg⟩ := hc ω M₀ M₁ hM₀ hw hω hs T hT
  have hh := (hn.add hf).add hg
  have ht := localization_total_error_le_masses ω M₁ hω hs T (by linarith)
  have he := hh.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  refine ⟨he,?_⟩
  have hL := localization_log_ge_one T hT
  calc
    _ ≤ ∑' v, (localizationRegionalMass .near ω T v+localizationRegionalMass .farCenter ω T v+localizationRegionalMass .farAnchor ω T v) := he.tsum_le_tsum ht hh
    _ = (∑' v, localizationRegionalMass .near ω T v)+(∑' v, localizationRegionalMass .farCenter ω T v)+(∑' v, localizationRegionalMass .farAnchor ω T v) := by rw [(hn.add hf).tsum_add hg,hn.tsum_add hf]
    _ ≤ A*(M₁:ℝ)*Real.log (2*T+2)^4/T+B*M₀*Real.log (2*T+2)^3/T+C*M₀*Real.log (2*T+2)^3/T := add_le_add (add_le_add bn bf) bg
    _ ≤ _ := by
      rw [← add_div, ← add_div]
      apply div_le_div_of_nonneg_right _ (by linarith : 0≤T)
      nlinarith [mul_nonneg hA.le (show 0≤M₀*Real.log (2*T+2)^3 by positivity),
        mul_nonneg hB.le (show 0≤(M₁:ℝ)*Real.log (2*T+2)^4 by positivity),
        mul_nonneg hC.le (show 0≤(M₁:ℝ)*Real.log (2*T+2)^4 by positivity)]

theorem tripleKernelLocalizationError_summed_bound_deriv :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ M₁ : ℝ), 0≤M₀ → 0≤M₁ →
      (∀ x, |ω x|≤M₀) → Differentiable ℝ ω → (∀ x, |deriv ω x|≤M₁) →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T →
      Summable (fun v : MasterTriple => ‖tripleKernelLocalizationError ω T v‖) ∧
      (∑' v : MasterTriple, ‖tripleKernelLocalizationError ω T v‖) ≤
        C*(M₁*Real.log (2*T+2)^4+M₀*Real.log (2*T+2)^3)/T := by
  obtain ⟨C,hC,hb⟩ := tripleKernelLocalizationError_summed_bound
  refine ⟨C,hC,fun ω M₀ M₁ hM₀ hM₁ hw hω hd hs T hT => ?_⟩
  apply hb ω M₀ ⟨M₁,hM₁⟩ hM₀ hw _ hs T hT
  exact lipschitzWith_of_nnnorm_deriv_le hω (fun x => by
    change ‖deriv ω x‖≤M₁
    simpa only [Real.norm_eq_abs] using hd x)

end
end HigherCorrelations
