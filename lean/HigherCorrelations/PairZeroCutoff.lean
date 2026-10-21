import HigherCorrelations.PairZeroUniformBounds

/-! UNCONDITIONAL cutoff optimization. No quantitative zero-free strip is used.
The optimized cutoff is admissible for T ≥ 5; smaller heights use Z = 10. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroCutoff_admissible (T : ℝ) (hT : 5 ≤ T) :
    2*T ≤ T*Real.log T^2 := by
  have hl : 3/2 ≤ Real.log T := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<5) hT
    linarith [Real.log_five_gt_d9]
  have hs : 2 ≤ Real.log T^2 := by nlinarith
  nlinarith

theorem pairZeroCutoff_log (T : ℝ) (hT : 5 ≤ T) :
    0 ≤ Real.log (T*Real.log T^2) ∧
    Real.log (T*Real.log T^2) ≤ 3*Real.log T := by
  have ht : 0 < T := by linarith
  have hl := (pairRHS_log_comparison T (by linarith)).1
  have hp : 0 < Real.log T := by linarith
  constructor
  · exact Real.log_nonneg (by linarith [pairZeroCutoff_admissible T hT])
  · rw [Real.log_mul ht.ne' (pow_pos hp 2).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have := Real.log_le_sub_one_of_pos hp
    linarith

theorem pairZero_error_triangle (X T Z : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
      |pairZeroTruncError X T Z| + |pairZeroHeightError X T Z| +
      |pairZeroExtensionError X T| := by
  rw [pairZero_decomposition X T Z hX hT hZ]
  have he : 2*Real.pi*(pairCorrelationSum X T).re + pairZeroTruncError X T Z +
      pairZeroHeightError X T Z + pairZeroExtensionError X T -
      2*Real.pi*(pairCorrelationSum X T).re =
      (pairZeroTruncError X T Z + pairZeroHeightError X T Z) +
      pairZeroExtensionError X T := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

theorem pairZeroCutoff_errors :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T : ℝ, 1 ≤ X → 5 ≤ T →
        |pairZeroTruncError X T (T*Real.log T^2)| ≤ Ctr*X ∧
        |pairZeroHeightError X T (T*Real.log T^2)| ≤
          Ch*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤
          Ce*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by
  obtain ⟨Ctr,Ch,Ce,htr,hh,he,hb⟩ := pairZeroUniformBounds
  refine ⟨9*Ctr,Ch,Ce,by positivity,hh,he,fun X T hX hT => ?_⟩
  obtain ⟨_,h₁,h₂,h₃,h₄⟩ := hb X T (T*Real.log T^2) hX (by linarith)
    (pairZeroCutoff_admissible T hT)
  refine ⟨h₁.trans ?_,h₂,h₃,h₄⟩
  have ht : 0 < T := by linarith
  have hl := (pairRHS_log_comparison T (by linarith)).1
  have hp : 0 < Real.log T := by linarith
  have hz := pairZeroCutoff_log T hT
  have hs : Real.log (T*Real.log T^2)^2 ≤ 9*Real.log T^2 := by nlinarith
  calc
    _ ≤ Ctr*X*T*(9*Real.log T^2)/(T*Real.log T^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _ = _ := by field_simp

theorem pairZeroComparison_smallHeight :
    ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T → T ≤ 5 →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤ C*X := by
  obtain ⟨Ctr,Ch,Ce,htr,hh,he,hb⟩ := pairZeroUniformBounds_envelope
  refine ⟨Ctr*Real.log 10^2+125*Ch+25*Ce,by positivity,fun X T hX hT ht => ?_⟩
  obtain ⟨_,h₁,h₂,h₃,_⟩ := hb X T 10 (1/2) hX hT (by linarith)
    (pairZeroHorizontalEnvelope_lt 10).le
  norm_num at h₂ h₃
  have hl := pairRHS_log_comparison T hT
  have hp : 0 ≤ Real.log T := by linarith [hl.1]
  have hu : Real.log T ≤ 5 := hl.2.1.trans ht
  have hs : Real.log T^2 ≤ 25 := by nlinarith
  have hc : Real.log T^3 ≤ 125 := by
    calc
      _ = Real.log T^2 * Real.log T := by ring
      _ ≤ 25*5 := mul_le_mul hs hu hp (by norm_num)
      _ = _ := by norm_num
  have a : |pairZeroTruncError X T 10| ≤ Ctr*Real.log 10^2*X := by
    apply h₁.trans
    have := mul_le_mul_of_nonneg_left (show T ≤ 10 by linarith)
      (show 0 ≤ Ctr*X*Real.log 10^2 by positivity)
    nlinarith
  have b : |pairZeroHeightError X T 10| ≤ 125*Ch*X := by
    apply h₂.trans
    nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ Ch*X by positivity)]
  have c : |pairZeroExtensionError X T| ≤ 25*Ce*X := by
    apply h₃.trans
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ Ce*X by positivity)]
  have := pairZero_error_triangle X T 10 hX (by linarith) (by norm_num)
  nlinarith

theorem pairZeroComparison_optimized :
    ∃ Cb Cx : ℝ, 0 < Cb ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
        Cb*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 + Cx*X := by
  obtain ⟨Ctr,Ch,Ce,htr,hh,he,hb⟩ := pairZeroCutoff_errors
  obtain ⟨Cs,hs,hsmall⟩ := pairZeroComparison_smallHeight
  refine ⟨Ch+Ce,Ctr+Cs,by positivity,by positivity,fun X T hX hT => ?_⟩
  have hl := (pairRHS_log_comparison T hT).1
  by_cases ht : 5 ≤ T
  · obtain ⟨a,b,c,_⟩ := hb X T hX ht
    have hz := pairZeroCutoff_admissible T ht
    have hd := pairZero_error_triangle X T (T*Real.log T^2) hX (by linarith) (by linarith)
    have hc : Real.log T^2 ≤ Real.log T^3 := by nlinarith [sq_nonneg (Real.log T-1)]
    have hw : 0 ≤ Ce*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2)) := by positivity
    have := mul_le_mul_of_nonneg_left hc hw
    have hx : 0 ≤ Cs*X := by positivity
    nlinarith
  · have := hsmall X T hX hT (by linarith)
    have hpos : 0 ≤ (Ch+Ce)*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 := by positivity
    have hx : 0 ≤ Ctr*X := by positivity
    nlinarith

end
end HigherCorrelations
