import HigherCorrelations.PairZeroExtensionBound

/-! UNCONDITIONAL named error budget. All constants precede all parameters;
no cutoff optimization or quantitative zero-free envelope is used here. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroTruncError_simple_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
      |pairZeroTruncError X T Z| ≤ C*X*T*Real.log Z^2/Z := by
  obtain ⟨C,hC,hb⟩ := pairZeroTruncError_bound
  refine ⟨2*C,by positivity,fun X T Z hX hT hZ => ?_⟩
  have hz : 1 ≤ Z := by linarith
  have hz0 : 0 < Z := by linarith
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hz
  have hl : Real.log (T+2) ≤ Real.log Z := Real.log_le_log (by linarith) (by linarith)
  have h₁ : Real.log (T+2)*Real.log Z/Z ≤ Real.log Z^2/Z :=
    div_le_div_of_nonneg_right (by nlinarith) hz0.le
  have h₂ : Real.log Z^2/Z^2 ≤ Real.log Z^2/Z :=
    div_le_div_of_nonneg_left (sq_nonneg _) hz0 (by nlinarith)
  calc
    _ ≤ C*X*T*(Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) := hb X T Z hX hT hZ
    _ ≤ C*X*T*(Real.log Z^2/Z+Real.log Z^2/Z) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity)
    _ = _ := by ring

theorem pairZeroUniformBounds :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T Z : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z →
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*
          (Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) ∧
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*Real.log Z^2/Z ∧
        |pairZeroHeightError X T Z| ≤ Ch*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤ Ce*X^(2*pairZeroHorizontalEnvelope Z)*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by
  obtain ⟨A,hA,ha⟩ := pairZeroTruncError_bound
  obtain ⟨B,hB,hb⟩ := pairZeroTruncError_simple_bound
  obtain ⟨Ch,hh,hheight⟩ := pairZeroHeightError_bound
  obtain ⟨Ce,he,hext⟩ := pairZeroExtensionError_bound
  refine ⟨A+B,Ch,Ce,by positivity,hh,he,fun X T Z hX hT hZ => ?_⟩
  have hz : 0<Z := by linarith
  have hl : 0≤Real.log (T+2) := Real.log_nonneg (by linarith)
  have hlz : 0≤Real.log Z := Real.log_nonneg (by linarith)
  refine ⟨(ha X T Z hX hT hZ).trans ?_,(hb X T Z hX hT hZ).trans ?_,
    hheight X T Z hX hT hZ,hext X T Z hX hT hZ,pairZeroExtensionError_nonpos X T⟩
  · have hp : 0≤B*X*T*(Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) := by positivity
    apply sub_nonneg.mp
    convert hp using 1 <;> ring
  · have hp : 0≤A*X*T*Real.log Z^2/Z := by positivity
    apply sub_nonneg.mp
    convert hp using 1 <;> ring

theorem pairZeroEnvelope_monotone_weight (X Z b : ℝ) (hX : 1 ≤ X)
    (hb : pairZeroHorizontalEnvelope Z ≤ b) :
    X^(2*pairZeroHorizontalEnvelope Z) ≤ X^(2*b) :=
  Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- The same three constants work for every larger horizontal envelope b. -/
theorem pairZeroUniformBounds_envelope :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T Z b : ℝ, 1 ≤ X → 3 ≤ T → 2*T ≤ Z → pairZeroHorizontalEnvelope Z ≤ b →
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*
          (Real.log (T+2)*Real.log Z/Z+Real.log Z^2/Z^2) ∧
        |pairZeroTruncError X T Z| ≤ Ctr*X*T*Real.log Z^2/Z ∧
        |pairZeroHeightError X T Z| ≤ Ch*X^(2*b)*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤ Ce*X^(2*b)*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by
  obtain ⟨Ctr,Ch,Ce,htr,hh,he,hb⟩ := pairZeroUniformBounds
  refine ⟨Ctr,Ch,Ce,htr,hh,he,fun X T Z b hX hT hZ hb' => ?_⟩
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hb X T Z hX hT hZ
  have hw := pairZeroEnvelope_monotone_weight X Z b hX hb'
  have hl : 0≤Real.log T := Real.log_nonneg (by linarith)
  exact ⟨h₁,h₂,h₃.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hh.le) (by positivity)),
    h₄.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw he.le) (sq_nonneg _)),h₅⟩

end
end HigherCorrelations
