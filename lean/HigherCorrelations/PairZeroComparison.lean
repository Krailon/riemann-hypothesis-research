import HigherCorrelations.PairZeroCutoff
import HigherCorrelations.HorizontalStrip

/-! UNCONDITIONAL uniform comparison, using the pinned PREPRINT strip theorem
QRH-STRIP-001. This is an alternative to the manuscript's classical KV route.
All total constants remain existential; only the absorption factor is explicit. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroHorizontalEnvelope_strip (Z : ℝ) :
    pairZeroHorizontalEnvelope Z ≤ 3/8 := by
  classical
  apply (Finset.max'_le_iff _ _).mpr
  intro d hd
  rcases Finset.mem_insert.mp hd with h|h
  · subst d; norm_num
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    have h := (zero_horizontal_strip i.1.property).2
    change (occurrenceValue i).re ≤ 7/8 at h
    unfold occurrenceDisplacement
    linarith

theorem pairZeroComparison_log_absorption (T : ℝ) (hT : 1 ≤ T) :
    Real.log T^3 ≤ 384*T^(1/4:ℝ) := by
  have ht : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have h := Real.pow_div_factorial_le_exp (Real.log T/4) (by positivity) 3
  norm_num at h
  rw [Real.rpow_def_of_pos ht]
  have he : Real.log T * (1/4:ℝ) = Real.log T/4 := by ring
  rw [he]
  nlinarith

theorem pairZeroComparison_weight_absorption (X T : ℝ) (hX : 1 ≤ X)
    (hXT : X ≤ T) : X^(3/4:ℝ)*Real.log T^3 ≤ 384*T := by
  have ht : 0 < T := by linarith
  have hw : X^(3/4:ℝ) ≤ T^(3/4:ℝ) :=
    Real.rpow_le_rpow (by linarith) hXT (by norm_num)
  have hl : 0 ≤ Real.log T := Real.log_nonneg (hX.trans hXT)
  calc
    _ ≤ T^(3/4:ℝ)*(384*T^(1/4:ℝ)) :=
      mul_le_mul hw (pairZeroComparison_log_absorption T (hX.trans hXT)) (by positivity) (by positivity)
    _ = 384*(T^(3/4:ℝ)*T^(1/4:ℝ)) := by ring
    _ = 384*T := by rw [← Real.rpow_add ht]; norm_num

theorem pairZeroComparison_strip_optimized :
    ∃ Cb Cx : ℝ, 0 < Cb ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
        Cb*X^(3/4:ℝ)*Real.log T^3 + Cx*X := by
  obtain ⟨Cb,Cx,hb,hx,h⟩ := pairZeroComparison_optimized
  refine ⟨Cb,Cx,hb,hx,fun X T hX hT => (h X T hX hT).trans ?_⟩
  have hw := pairZeroEnvelope_monotone_weight X (T*Real.log T^2) (3/8) hX
    (pairZeroHorizontalEnvelope_strip _)
  norm_num at hw
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hw hb.le) (by positivity)) le_rfl

theorem pairZeroComparison_uniform_errors :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T : ℝ, 1 ≤ X → 5 ≤ T → X ≤ T →
        |pairZeroTruncError X T (T*Real.log T^2)| ≤ Ctr*X ∧
        |pairZeroHeightError X T (T*Real.log T^2)| ≤ Ch*T ∧
        |pairZeroExtensionError X T| ≤ Ce*T ∧ pairZeroExtensionError X T ≤ 0 := by
  obtain ⟨Ctr,Ch,Ce,htr,hh,he,hb⟩ := pairZeroCutoff_errors
  refine ⟨Ctr,384*Ch,384*Ce,htr,by positivity,by positivity,fun X T hX hT hXT => ?_⟩
  obtain ⟨a,b,c,d⟩ := hb X T hX hT
  have hw := pairZeroEnvelope_monotone_weight X (T*Real.log T^2) (3/8) hX
    (pairZeroHorizontalEnvelope_strip _)
  norm_num at hw
  have hl := (pairRHS_log_comparison T (by linarith)).1
  have hc : Real.log T^2 ≤ Real.log T^3 := by nlinarith [sq_nonneg (Real.log T-1)]
  have hab := pairZeroComparison_weight_absorption X T hX hXT
  have hh' : X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 ≤ 384*T :=
    (mul_le_mul_of_nonneg_right hw (by positivity)).trans hab
  have he' : X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^2 ≤ 384*T :=
    (mul_le_mul_of_nonneg_left hc (by positivity)).trans hh'
  refine ⟨a,?_,?_,d⟩
  · nlinarith [mul_le_mul_of_nonneg_left hh' hh.le]
  · nlinarith [mul_le_mul_of_nonneg_left he' he.le]

theorem pairZeroComparison_uniform :
    ∃ Ct Cx : ℝ, 0 < Ct ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T → X ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤ Ct*T+Cx*X := by
  obtain ⟨Cb,Cx,hb,hx,h⟩ := pairZeroComparison_strip_optimized
  refine ⟨384*Cb,Cx,by positivity,hx,fun X T hX hT hXT => ?_⟩
  have := h X T hX hT
  have := mul_le_mul_of_nonneg_left (pairZeroComparison_weight_absorption X T hX hXT) hb.le
  nlinarith

end
end HigherCorrelations
