import HigherCorrelations.PairZeroHeightBound

/-! UNCONDITIONAL extension bound with its nonpositive sign. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZeroExtensionError_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroExtensionError X T| ≤ C*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^2 := by
  obtain ⟨D,hD,hd⟩ := zeroKernel_interior_bound
  refine ⟨32*((4/3:ℝ)*D)^2,by positivity,fun X T Z hX hT hZ => ?_⟩
  have hT0 : 0≤T := by linarith
  have hX0 : 0<X := by linarith
  let w := X^(pairZeroHorizontalEnvelope Z)
  have hw : 0 ≤ w := Real.rpow_nonneg hX0.le _
  have hw2 : w^2 = X^(2*pairZeroHorizontalEnvelope Z) := pairZeroWeight_square _ _ hX0
  have hL : 0 ≤ Real.log (T+2) := Real.log_nonneg (by linarith)
  let K := ((4/3:ℝ)*D)^2*w^2*Real.log (T+2)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hp (t : ℝ) (ht : t ∈ (Set.Icc (0:ℝ) T)ᶜ) :
      ‖‖pairZeroWindowVector X T t‖^2‖ ≤ K*pairZeroExtensionProfile T t := by
    have ht' : t≤0 ∨ T≤t := by
      simp only [Set.mem_compl_iff,Set.mem_Icc,not_and_or,not_le] at ht
      exact ht.imp le_of_lt le_of_lt
    have hdist : 0 ≤ heightIntervalDistance T t := (heightIntervalDistance_geometry T t hT0 ht').1
    have hv : ‖pairZeroWindowVector X T t‖ ≤
        (4/3:ℝ)*w*(D*Real.log (T+2)/(1+heightIntervalDistance T t)) :=
      (pairZeroWindow_exterior_majorant X T Z t hX hT0 (by linarith)).trans
        (mul_le_mul_of_nonneg_left (hd T t hT ht') (by positivity))
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ((4/3:ℝ)*w*(D*Real.log (T+2)/(1+heightIntervalDistance T t)))^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hv 2
      _ = _ := by dsimp [K,pairZeroExtensionProfile]; ring
  obtain ⟨hi,he⟩ := pairZeroExtensionProfile_integral T hT0
  have hb := norm_integral_le_of_norm_le (hi.const_mul K)
    ((ae_restrict_mem measurableSet_Icc.compl).mono (fun t ht => hp t ht))
  rw [integral_const_mul,he,Real.norm_eq_abs] at hb
  have hlog := (pairRHS_log_comparison T hT).2.2.2.2
  have hs : Real.log (T+2)^2 ≤ 4*Real.log T^2 := by
    have hh := sq_le_sq₀ hL (show 0≤2*Real.log T by linarith [(pairRHS_log_comparison T hT).1]) |>.mpr hlog
    nlinarith
  unfold pairZeroExtensionError
  rw [abs_mul]
  rw [show |(-4:ℝ)| = 4 by norm_num]
  calc
    _ ≤ 4*(K*2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (8*((4/3:ℝ)*D)^2*w^2)*Real.log (T+2)^2 := by dsimp [K]; ring
    _ ≤ (8*((4/3:ℝ)*D)^2*w^2)*(4*Real.log T^2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [hw2]; ring

end
end HigherCorrelations
