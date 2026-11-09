import HigherCorrelations.DensityCountIdentities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Conditional density adapters. Every analytic count bound takes an explicit
`UniformDyadicDensity C T₀` argument. No instance of that hypothesis is supplied.
Finite covers, exponential identities and monotonicity are UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open scoped Classical

theorem densityInterval_dyadic_cover (T D : ℝ) (hT : 0 < T) :
    (rightDensityInterval (T/2) (5*T/2) D).card ≤
      (rightDensityWindow (T/4) (T/2) D).card +
      (rightDensityWindow (T/2) T D).card +
      (rightDensityWindow T (2*T) D).card +
      (rightDensityWindow (2*T) (4*T) D).card := by
  let A := rightDensityWindow (T/4) (T/2) D
  let B := rightDensityWindow (T/2) T D
  let C := rightDensityWindow T (2*T) D
  let E := rightDensityWindow (2*T) (4*T) D
  have hcover : rightDensityInterval (T/2) (5*T/2) D ⊆ A ∪ B ∪ C ∪ E := by
    intro i hi
    rcases (mem_rightDensityInterval _ _ _ _).mp hi with ⟨hl,hu,hd⟩
    simp only [Finset.mem_union]
    by_cases h1 : occurrenceOrdinate i ≤ T/2
    · exact Or.inl (Or.inl (Or.inl ((mem_rightDensityWindow _ _ _ _).mpr ⟨by linarith,h1,hd⟩)))
    by_cases h2 : occurrenceOrdinate i ≤ T
    · exact Or.inl (Or.inl (Or.inr ((mem_rightDensityWindow _ _ _ _).mpr ⟨lt_of_not_ge h1,h2,hd⟩)))
    by_cases h3 : occurrenceOrdinate i ≤ 2*T
    · exact Or.inl (Or.inr ((mem_rightDensityWindow _ _ _ _).mpr ⟨lt_of_not_ge h2,h3,hd⟩))
    · exact Or.inr ((mem_rightDensityWindow _ _ _ _).mpr ⟨lt_of_not_ge h3,by linarith,hd⟩)
  have hc := Finset.card_le_card hcover
  have h1 := Finset.card_union_le (A ∪ B ∪ C) E
  have h2 := Finset.card_union_le (A ∪ B) C
  have h3 := Finset.card_union_le A B
  change (rightDensityInterval (T/2) (5*T/2) D).card ≤ A.card+B.card+C.card+E.card
  omega

private theorem density_window_compare (C T₀ T V D : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hV : T/4 ≤ V) (hV' : V ≤ 2*T) (hD : 0 ≤ D) (hD' : D ≤ 331/1000) :
    ((rightDensityWindow V (2*V) D).card : ℝ) ≤
      4*C*(T^(1-D/4)*Real.log T+(Real.log T)^2) := by
  have hT₀ := h.threshold_ge_three
  have hC := h.constant_pos
  have ht : 0 < T := by linarith
  have hv : T₀ ≤ V := by linarith
  have hv0 : 0 < V := by linarith
  have hp0 : 0 ≤ 1-D/4 := by linarith
  have hp1 : 1-D/4 ≤ 1 := by linarith
  have hpow : V^(1-D/4) ≤ 2*T^(1-D/4) := by
    calc
      _ ≤ (2*T)^(1-D/4) := Real.rpow_le_rpow hv0.le hV' hp0
      _ = (2:ℝ)^(1-D/4)*T^(1-D/4) := Real.mul_rpow (by norm_num) ht.le
      _ ≤ 2*T^(1-D/4) := by
        gcongr
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hp1
  have hlog0 : 0 ≤ Real.log V := Real.log_nonneg (by linarith)
  have hq0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hl : Real.log V ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (2*T) := Real.log_le_log hv0 hV'
      _ = Real.log 2+Real.log T := Real.log_mul (by norm_num) ht.ne'
      _ ≤ _ := by
        have := Real.log_le_log (by norm_num : (0:ℝ) < 2) (show 2 ≤ T by linarith)
        linarith
  have hprod := mul_le_mul hpow hl hlog0 (by positivity : 0 ≤ 2*T^(1-D/4))
  have hsquare := pow_le_pow_left₀ hlog0 hl 2
  have hh := h.bound V D hv hD hD'
  have hsum : V^(1-D/4)*Real.log V+(Real.log V)^2 ≤
      4*(T^(1-D/4)*Real.log T+(Real.log T)^2) := by nlinarith
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum hC.le])

theorem density_comparable_interval (C T₀ T D : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hD : 0 ≤ D) (hD' : D ≤ 331/1000) :
    ((horizontalDensityInterval (T/2) (5*T/2) D).card : ℝ) ≤
      32*C*(T^(1-D/4)*Real.log T+(Real.log T)^2) := by
  have ht₀ := h.threshold_ge_three
  have ht : 0 < T := by linarith
  have h1 := density_window_compare C T₀ T (T/4) D h hT le_rfl (by linarith) hD hD'
  have h2 := density_window_compare C T₀ T (T/2) D h hT (by linarith) (by linarith) hD hD'
  have h3 := density_window_compare C T₀ T T D h hT (by linarith) (by linarith) hD hD'
  have h4 := density_window_compare C T₀ T (2*T) D h hT (by linarith) le_rfl hD hD'
  have he1 : 2*(T/4)=T/2 := by ring
  have he2 : 2*(T/2)=T := by ring
  have he4 : 2*(2*T)=4*T := by ring
  rw [he1] at h1
  rw [he2] at h2
  rw [he4] at h4
  have hc := densityInterval_dyadic_cover T D ht
  have hc' : ((rightDensityInterval (T/2) (5*T/2) D).card : ℝ) ≤
      (rightDensityWindow (T/4) (T/2) D).card + (rightDensityWindow (T/2) T D).card +
      (rightDensityWindow T (2*T) D).card + (rightDensityWindow (2*T) (4*T) D).card := by
    exact_mod_cast hc
  rw [horizontalDensityInterval_twice_right _ _ _ hD, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem density_power_exp (T v : ℝ) (hT : 1 < T) :
    T^(1-(v/Real.log T)/4) = T*Real.exp (-v/4) := by
  have ht : 0 < T := by linarith
  have hq : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  rw [Real.rpow_def_of_pos ht]
  have he : Real.log T*(1-(v/Real.log T)/4) = Real.log T+(-v/4) := by field_simp; ring
  rw [he, Real.exp_add, Real.exp_log ht]

theorem density_scaled_tail_bound (C T₀ T v : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hv : 0 ≤ v) (hv' : v ≤ (331/1000)*Real.log T) :
    (densityScaledTail T v : ℝ) ≤
      32*C*(T*Real.log T*Real.exp (-v/4)+(Real.log T)^2) := by
  have ht₀ := h.threshold_ge_three
  have ht : 1 < T := by linarith
  have hq : 0 < Real.log T := Real.log_pos ht
  have hh := density_comparable_interval C T₀ T (v/Real.log T) h hT
    (div_nonneg hv hq.le) ((div_le_iff₀ hq).mpr hv')
  rw [density_power_exp T v ht] at hh
  simpa only [densityScaledTail, mul_assoc, mul_left_comm, mul_comm] using hh

theorem density_scaled_tail_antitone (T : ℝ) (hT : 1 < T) :
    Antitone (densityScaledTail T) := by
  intro v w hvw
  exact Finset.card_le_card (horizontalDensityInterval_mono le_rfl le_rfl
    (div_le_div_of_nonneg_right hvw (Real.log_pos hT).le))

theorem density_scaled_tail_endpoint (C T₀ T : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T) :
    (densityScaledTail T ((331/1000)*Real.log T) : ℝ) ≤
      32*C*(T^((1:ℝ)-331/4000)*Real.log T+(Real.log T)^2) := by
  have ht₀ := h.threshold_ge_three
  have hq : Real.log T ≠ 0 := ne_of_gt (Real.log_pos (by linarith : 1 < T))
  have hh := density_comparable_interval C T₀ T (331/1000) h hT (by norm_num) le_rfl
  norm_num [densityScaledTail, hq] at hh ⊢
  exact hh

theorem density_scaled_tail_frozen (C T₀ T v : ℝ)
    (h : UniformDyadicDensity C T₀) (hT : 4*T₀ ≤ T)
    (hv : (331/1000)*Real.log T ≤ v) :
    (densityScaledTail T v : ℝ) ≤
      32*C*(T^((1:ℝ)-331/4000)*Real.log T+(Real.log T)^2) := by
  have ht₀ := h.threshold_ge_three
  exact (Nat.cast_le.mpr (density_scaled_tail_antitone T (by linarith) hv)).trans
    (density_scaled_tail_endpoint C T₀ T h hT)

end
end HigherCorrelations
