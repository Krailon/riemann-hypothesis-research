import HigherCorrelations.PairNormalizedSymmetry
import HigherCorrelations.PairNormalizedAssembly

/-! UNCONDITIONAL normalized pair asymptotic, using the pinned PREPRINT strip
through the comparison. Constants are existential, uniformly on the closed range.
The origin retains its separate O(1) peak error. -/
namespace HigherCorrelations
noncomputable section

theorem pairNormalized_power (T α : ℝ) (hT : 3 ≤ T) (ha : 0 ≤ α) (ha1 : α ≤ 1) :
    1 ≤ T^α ∧ T^α ≤ T ∧ Real.log (T^α)/Real.log T = α ∧
    1/(T^α)^2 = T^(-2*α) := by
  have ht : 0<T := by linarith
  have hl : Real.log T ≠ 0 := ne_of_gt (by linarith [(pairRHS_log_comparison T hT).1])
  refine ⟨Real.one_le_rpow (by linarith) ha,?_,?_,?_⟩
  · simpa using Real.rpow_le_rpow_of_exponent_le (show 1≤T by linarith) ha1
  · rw [Real.log_rpow ht]; field_simp
  · rw [show -2*α = -(α*2) by ring,Real.rpow_neg ht.le,Real.rpow_mul ht.le,Real.rpow_two,one_div]

theorem pairNormalized_nonnegative_frequency :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ T α : ℝ, 3≤T → 0≤α → α≤1 →
      |pairNormalizedCorrelation T α - T^(-2*α)*Real.log T - α| ≤
        C₁*T^(-2*α)+C₂/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,hA,hB,h⟩ := pairNormalized_base_bound
  refine ⟨A,B,hA,hB,fun T α hT ha ha1 => ?_⟩
  obtain ⟨hX,hXT,hlog,hpow⟩ := pairNormalized_power T α hT ha ha1
  have hb := h (T^α) T hX hT hXT
  have he : Real.log T/(T^α)^2 = T^(-2*α)*Real.log T := by rw [div_eq_mul_one_div,hpow]; ring
  have hc : A/(T^α)^2 = A*T^(-2*α) := by rw [div_eq_mul_one_div,hpow]
  rw [he,hc,hlog] at hb
  simpa only [pairNormalizedCorrelation,sub_sub] using hb

theorem pairNormalized_asymptotic :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ T α : ℝ, 3≤T → |α|≤1 →
      |pairNormalizedCorrelation T α - T^(-2*|α|)*Real.log T - (|α|)| ≤
        C₁*T^(-2*|α|)+C₂/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,hA,hB,h⟩ := pairNormalized_nonnegative_frequency
  refine ⟨A,B,hA,hB,fun T α hT ha => ?_⟩
  have hb := h T |α| hT (abs_nonneg _) ha
  rwa [pairNormalizedCorrelation_abs T α (by linarith)] at hb

theorem pairNormalized_origin :
    ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 3≤T →
      |pairNormalizedCorrelation T 0-Real.log T| ≤ C := by
  obtain ⟨A,B,hA,hB,h⟩ := pairNormalized_asymptotic
  refine ⟨A+B,by positivity,fun T hT => ?_⟩
  have hb := h T 0 hT (by norm_num)
  norm_num at hb
  have hs := (pairRHS_height_scales 1 T (by norm_num) hT (by linarith)).2.1
  exact hb.trans (add_le_add le_rfl (div_le_self hB.le hs))

theorem pairNormalized_endpoint_scales (T : ℝ) (hT : 3 ≤ T) :
    T^(-2:ℝ)*Real.log T ≤ 1/Real.sqrt (Real.log T) ∧
    T^(-2:ℝ) ≤ 1/Real.sqrt (Real.log T) := by
  have ht : 0<T := by linarith
  obtain ⟨hl,hlt,_,_,_⟩ := pairRHS_log_comparison T hT
  have hl0 : 0<Real.log T := by linarith
  have hs0 : 0<Real.sqrt (Real.log T) := Real.sqrt_pos.mpr hl0
  have hs2 := Real.sq_sqrt hl0.le
  have hsT : Real.sqrt (Real.log T) ≤ T := by nlinarith [Real.sqrt_nonneg (Real.log T)]
  have hprod : Real.log T*Real.sqrt (Real.log T) ≤ T^2 := by
    nlinarith [mul_le_mul hlt hsT hs0.le ht.le]
  have hpow : T^(-2:ℝ) = 1/T^2 := by rw [Real.rpow_neg ht.le,Real.rpow_two,one_div]
  rw [hpow]
  constructor
  · rw [div_mul_eq_mul_div,one_mul]
    exact (div_le_div_iff₀ (sq_pos_of_pos ht) hs0).mpr (by simpa using hprod)
  · exact (one_div_le_one_div_of_le hs0 (by nlinarith))

theorem pairNormalized_endpoints :
    ∃ C : ℝ, 0<C ∧ ∀ T α : ℝ, 3≤T → |α|=1 →
      |pairNormalizedCorrelation T α-1| ≤ C/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,hA,hB,h⟩ := pairNormalized_asymptotic
  refine ⟨A+B+1,by positivity,fun T α hT ha => ?_⟩
  have hb := h T α hT (by rw [ha])
  rw [ha] at hb
  norm_num only [mul_one] at hb
  obtain ⟨hs,hp⟩ := pairNormalized_endpoint_scales T hT
  have hq : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have ht : 0<T := by linarith
  have hpeak : 0 ≤ T^(-2:ℝ)*Real.log T := by positivity
  have he : pairNormalizedCorrelation T α-1 =
      (pairNormalizedCorrelation T α-T^(-2:ℝ)*Real.log T-1)+T^(-2:ℝ)*Real.log T := by ring
  rw [he]
  have hab := abs_add_le (pairNormalizedCorrelation T α-T^(-2:ℝ)*Real.log T-1) (T^(-2:ℝ)*Real.log T)
  rw [abs_of_nonneg hpeak] at hab
  have hh := mul_le_mul_of_nonneg_left hp hA.le
  simp only [div_eq_mul_inv] at hb hs hh ⊢
  nlinarith

theorem pairNormalized_minimal_height :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ α : ℝ, |α|≤1 →
      |pairNormalizedCorrelation 3 α - (3:ℝ)^(-2*|α|)*Real.log 3 - (|α|)| ≤
        C₁*(3:ℝ)^(-2*|α|)+C₂/Real.sqrt (Real.log 3) := by
  obtain ⟨A,B,hA,hB,h⟩ := pairNormalized_asymptotic
  exact ⟨A,B,hA,hB,fun α ha => h 3 α (by norm_num) ha⟩

end
end HigherCorrelations
