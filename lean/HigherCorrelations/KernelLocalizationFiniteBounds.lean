import HigherCorrelations.KernelLocalizationAnchorBounds

/-! UNCONDITIONAL finite regional integral-norm estimates. The finite-cutoff
route proves uniform bounds before removing any occurrence cutoff. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem localization_Q_nonneg (t : ℝ) : 0≤zeroKernelSum t :=
  tsum_nonneg (fun _ => ordinateKernel_nonneg _)

theorem localization_Q_local :
    ∃ C : ℝ, 0<C ∧ ∀ T t : ℝ, 3≤T → t ∈ Icc 0 (3*T) →
      zeroKernelSum t ≤ C*Real.log (2*T+2) := by
  obtain ⟨C,hC,hb⟩ := zeroKernel_summable_bound
  refine ⟨2*C,by positivity,fun T t hT ht => ?_⟩
  have hx : |t|≤4*T+2 := by rw [abs_of_nonneg ht.1]; linarith [ht.2]
  exact (hb t).2.trans ((mul_le_mul_of_nonneg_left (localization_local_log T t hT hx) hC.le).trans_eq (by ring))

theorem localization_anchor_count :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 3≤T →
      ((occurrenceInterval T (2*T)).card:ℝ) ≤ C*T*Real.log (2*T+2) := by
  obtain ⟨C,hC,hb⟩ := occurrence_count_interval
  refine ⟨2*C,by positivity,fun T hT => ?_⟩
  have h := hb T (2*T) (by linarith)
  rw [abs_of_nonneg (by linarith : 0≤T),abs_of_nonneg (by linarith : 0≤2*T),max_eq_right (by linarith)] at h
  have hL := localization_log_ge_one T hT
  nlinarith [mul_nonneg (show 0≤C*Real.log (2*T+2) by positivity) (show 0≤T-1 by linarith)]

theorem localization_mass_of_indicator_bound (r : LocalizationRegion) (ω : ℝ → ℝ)
    (M : ℝ≥0) (hω : LipschitzWith M ω) (T : ℝ) (hT : 0<T)
    (D : Finset MasterTriple) (a b A : ℝ) (hab : a≤b)
    (hb : ∀ t, (∑ v ∈ D, ‖localizationRegionalDensity r ω T v t‖) ≤ (Icc a b).indicator (fun _ => A) t) :
    (∑ v ∈ D, localizationRegionalMass r ω T v) ≤ (b-a)*A := by
  have hi (v : MasterTriple) := (localizationRegionalDensity_integrable r ω M hω T hT v).norm
  have hj : Integrable ((Icc a b).indicator (fun _ : ℝ => A)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr continuous_const.integrableOn_Icc
  have hh := integral_mono (integrable_finsetSum _ (fun v _ => hi v)) hj hb
  rw [integral_finsetSum _ (fun v _ => hi v),integral_indicator_const _ measurableSet_Icc,
    Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hab), smul_eq_mul] at hh
  exact hh

private def tuple_support (D : Finset MasterTriple) : Finset ZeroOccurrence := by
  classical
  exact D.biUnion (fun v => Finset.univ.image v)

private theorem tuple_support_mem (D : Finset MasterTriple) (v : MasterTriple) (hv : v∈D) (r : Fin 3) :
    v r ∈ tuple_support D := by
  classical
  exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩⟩

theorem localization_near_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M : ℝ≥0), LipschitzWith M ω →
      Function.support ω ⊆ Icc (1:ℝ) 2 → ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .near ω T v) ≤
        C*(M:ℝ)*Real.log (2*T+2)^4/T := by
  classical
  obtain ⟨Q,hQ,hq⟩ := localization_Q_local
  obtain ⟨C,hC,hc⟩ := localization_near_anchor_sum
  refine ⟨3*(64/27)*Q^2*C,by positivity,fun ω M hw hs T hT D => ?_⟩
  let A := (64/27)*Q^2*C*(M:ℝ)*Real.log (2*T+2)^4/T^2
  have hp (t : ℝ) : (∑ v ∈ D, ‖localizationRegionalDensity .near ω T v t‖) ≤
      (Icc (0:ℝ) (3*T)).indicator (fun _ => A) t := by
    have h := localization_finite_majorant .near ω T (by linarith) D (tuple_support D) (tuple_support_mem D) t
    by_cases ht : t∈Icc (0:ℝ) (3*T)
    · rw [Set.indicator_of_mem ht]
      have h₁ := hq T t hT ht
      have h₂ := hc ω M hw T t hT ht (tuple_support D)
      have hL := localization_log_ge_one T hT
      calc
        _ ≤ (64/(27*T))*(zeroKernelSum t)^2*(∑ i ∈ tuple_support D, localizationAnchorWeight .near ω T t i) := h
        _ ≤ (64/(27*T))*(Q*Real.log (2*T+2))^2*(C*(M:ℝ)*Real.log (2*T+2)^2/T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (localization_Q_nonneg t) h₁ 2) (by positivity))
            h₂ (Finset.sum_nonneg (fun i _ => localizationAnchorWeight_nonneg _ _ _ _ _)) (by positivity)
        _ = A := by dsimp [A]; ring
    · rw [Set.indicator_of_notMem ht]
      simpa only [localization_near_weight_zero ω hs T t (by linarith) ht,Finset.sum_const_zero,mul_zero] using h
  have h := localization_mass_of_indicator_bound .near ω M hw T (by linarith) D 0 (3*T) A (by linarith) hp
  apply h.trans_eq
  dsimp [A]
  field_simp
  <;> ring

theorem localization_far_center_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .farCenter ω T v) ≤
        C*M₀*Real.log (2*T+2)^3/T := by
  classical
  obtain ⟨Q,hQ,hq⟩ := localization_Q_local
  obtain ⟨C,hC,hc⟩ := localization_far_center_anchor_sum
  refine ⟨(64/27)*Q^2*C,by positivity,fun ω M₀ M₁ hM₀ hw hω T hT D => ?_⟩
  let A := (64/27)*Q^2*C*M₀*Real.log (2*T+2)^3/T^2
  have hp (t : ℝ) : (∑ v ∈ D, ‖localizationRegionalDensity .farCenter ω T v t‖) ≤
      (Icc T (2*T)).indicator (fun _ => A) t := by
    have h := localization_finite_majorant .farCenter ω T (by linarith) D (tuple_support D) (tuple_support_mem D) t
    by_cases ht : t∈Icc T (2*T)
    · rw [Set.indicator_of_mem ht]
      have h₁ := hq T t hT ⟨by linarith [ht.1],by linarith [ht.2]⟩
      have h₂ := hc ω M₀ hM₀ hw T t hT ht (tuple_support D)
      have hL := localization_log_ge_one T hT
      calc
        _ ≤ (64/(27*T))*(zeroKernelSum t)^2*(∑ i ∈ tuple_support D, localizationAnchorWeight .farCenter ω T t i) := h
        _ ≤ (64/(27*T))*(Q*Real.log (2*T+2))^2*(C*M₀*Real.log (2*T+2)/T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (localization_Q_nonneg t) h₁ 2) (by positivity))
            h₂ (Finset.sum_nonneg (fun i _ => localizationAnchorWeight_nonneg _ _ _ _ _)) (by positivity)
        _ = A := by dsimp [A]; ring
    · rw [Set.indicator_of_notMem ht]
      have he (i : ZeroOccurrence) : localizationAnchorWeight .farCenter ω T t i=0 := by
        unfold localizationAnchorWeight
        apply Set.indicator_of_notMem
        exact fun hi => ht hi.2
      simpa only [he,Finset.sum_const_zero,mul_zero] using h
  have h := localization_mass_of_indicator_bound .farCenter ω M₁ hω T (by linarith) D T (2*T) A (by linarith) hp
  apply h.trans_eq
  dsimp [A]
  field_simp
  <;> ring

end
end HigherCorrelations
