import HigherCorrelations.KernelLocalizationFiniteBounds
import HigherCorrelations.KernelLocalizationTail

/-! UNCONDITIONAL far-anchor budget. The centers are integrated over the whole
real line; only the anchor occurrence is confined to the height interval. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped NNReal

theorem localization_far_anchor_weight (Q : ℝ) (hQ : 0<Q)
    (hq : ∀ t, zeroKernelSum t ≤ Q*Real.log (|t|+2))
    (ω : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hw : ∀ x, |ω x|≤M)
    (hs : Function.support ω ⊆ Icc (1:ℝ) 2) (T t : ℝ) (hT : 3≤T) (i : ZeroOccurrence) :
    (zeroKernelSum t)^2*localizationAnchorWeight .farAnchor ω T t i ≤
      (if i ∈ occurrenceInterval T (2*T) then
        (4*Q^2*M*Real.log (2*T+2)^2/T^2)*localizationTailProfile ((t-occurrenceOrdinate i)/T) else 0) := by
  classical
  by_cases hr : t ∈ localizationRegionSet .farAnchor T (occurrenceOrdinate i)
  · have ht : T< |t-occurrenceOrdinate i| ∧ t∉Icc T (2*T) ∧ occurrenceOrdinate i∈Icc T (2*T) := hr
    have hi := (mem_occurrenceInterval _ _ i).mpr ht.2.2
    rw [if_pos hi,localizationAnchorWeight,Set.indicator_of_mem hr,
      localization_weight_zero ω hs T t (by linarith) ht.2.1,zero_sub,abs_neg]
    have hb := localization_tail_scaled_bound T (occurrenceOrdinate i) t hT ht.2.2 ht.1
    have hlog : 0≤Real.log (|t|+2) := Real.log_nonneg (by nlinarith [abs_nonneg t])
    have hp := pow_le_pow_left₀ (localization_Q_nonneg t) (hq t) 2
    calc
      _ ≤ (Q*Real.log (|t|+2))^2*(ordinateKernel (t-occurrenceOrdinate i)*M) :=
        mul_le_mul hp (mul_le_mul_of_nonneg_left (hw _) (ordinateKernel_nonneg _))
          (mul_nonneg (ordinateKernel_nonneg _) (abs_nonneg _)) (sq_nonneg _)
      _ = Q^2*M*(Real.log (|t|+2)^2*ordinateKernel (t-occurrenceOrdinate i)) := by ring
      _ ≤ Q^2*M*((4*Real.log (2*T+2)^2/T^2)*localizationTailProfile ((t-occurrenceOrdinate i)/T)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  · rw [localizationAnchorWeight,Set.indicator_of_notMem hr,mul_zero]
    split_ifs
    · exact mul_nonneg (by positivity) (localizationTailProfile_nonneg _)
    · exact le_rfl

theorem localization_far_anchor_finite_mass :
    ∃ C : ℝ, 0<C ∧ ∀ (ω : ℝ → ℝ) (M₀ : ℝ) (M₁ : ℝ≥0), 0≤M₀ →
      (∀ x, |ω x|≤M₀) → LipschitzWith M₁ ω → Function.support ω ⊆ Icc (1:ℝ) 2 →
      ∀ T : ℝ, 3≤T → ∀ D : Finset MasterTriple,
      (∑ v ∈ D, localizationRegionalMass .farAnchor ω T v) ≤
        C*M₀*Real.log (2*T+2)^3/T := by
  classical
  obtain ⟨Q,hQ,hq⟩ := zeroKernel_summable_bound
  obtain ⟨C,hC,hc⟩ := localization_anchor_count
  let J := ∫ u : ℝ, localizationTailProfile u
  have hJ : 0≤J := integral_nonneg localizationTailProfile_nonneg
  refine ⟨(256/27)*Q^2*C*(J+1),by positivity,fun ω M₀ M₁ hM₀ hw hω hs T hT D => ?_⟩
  let s := D.biUnion (fun v => Finset.univ.image v)
  have hsub (v : MasterTriple) (hv : v∈D) (r : Fin 3) : v r∈s :=
    Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩⟩
  let B := 4*Q^2*M₀*Real.log (2*T+2)^2/T^2
  let A := (64/(27*T))*B
  let P := fun t : ℝ => ∑ i ∈ occurrenceInterval T (2*T), localizationTailProfile ((t-occurrenceOrdinate i)/T)
  have hB : 0≤B := by dsimp [B]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hP : Integrable P := integrable_finsetSum _ (fun i _ => localization_scaled_profile_integrable T _ (by linarith))
  have hp (t : ℝ) : (∑ v ∈ D, ‖localizationRegionalDensity .farAnchor ω T v t‖) ≤ A*P t := by
    have h := localization_finite_majorant .farAnchor ω T (by linarith) D s hsub t
    have hb : (zeroKernelSum t)^2*(∑ i ∈ s, localizationAnchorWeight .farAnchor ω T t i) ≤ B*P t := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ i ∈ s, if i∈occurrenceInterval T (2*T) then B*localizationTailProfile ((t-occurrenceOrdinate i)/T) else 0 :=
          Finset.sum_le_sum (fun i _ => localization_far_anchor_weight Q hQ (fun t => (hq t).2) ω M₀ hM₀ hw hs T t hT i)
        _ = ∑ i ∈ s with i∈occurrenceInterval T (2*T), B*localizationTailProfile ((t-occurrenceOrdinate i)/T) := (Finset.sum_filter _ _).symm
        _ ≤ ∑ i ∈ occurrenceInterval T (2*T), B*localizationTailProfile ((t-occurrenceOrdinate i)/T) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).2)
            (fun i _ _ => mul_nonneg hB (localizationTailProfile_nonneg _))
        _ = _ := (Finset.mul_sum _ _ _).symm
    apply h.trans
    dsimp [A]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : 0≤64/(27*T))
  have hi (v : MasterTriple) := (localizationRegionalDensity_integrable .farAnchor ω M₁ hω T (by linarith) v).norm
  have hh := integral_mono (integrable_finsetSum _ (fun v _ => hi v)) (hP.const_mul A) hp
  rw [integral_finsetSum _ (fun v _ => hi v),integral_const_mul] at hh
  have hPi : (∫ t : ℝ, P t)=((occurrenceInterval T (2*T)).card:ℝ)*(T*J) := by
    dsimp [P]
    rw [integral_finsetSum _ (fun i _ => localization_scaled_profile_integrable T _ (by linarith))]
    simp only [localization_scaled_profile_integral T _ (by linarith),Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [hPi] at hh
  have hL := localization_log_ge_one T hT
  calc
    _ ≤ A*(((occurrenceInterval T (2*T)).card:ℝ)*(T*J)) := hh
    _ ≤ A*((C*T*Real.log (2*T+2))*(T*J)) := by gcongr; exact hc T hT
    _ ≤ A*((C*T*Real.log (2*T+2))*(T*(J+1))) := by gcongr; linarith
    _ = _ := by dsimp [A,B]; field_simp <;> ring

end
end HigherCorrelations
