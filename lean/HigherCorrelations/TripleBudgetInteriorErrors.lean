import HigherCorrelations.TripleBudgetInteriorRemainders
import HigherCorrelations.TripleBudgetLowWords
import HigherCorrelations.TripleBudgetOffDiagonalRates

/-! UNCONDITIONAL common-height bounds used when combining the eight named errors. -/
namespace HigherCorrelations
noncomputable section

theorem tripleBudgetOmega_height (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T : ℝ) (hT : 3≤T) :
    tripleBudgetOmega ω T 1 ≤ (1+fourierDerivativeL1 ω 1)*Real.log (2*T+2) ∧
    tripleBudgetOmega ω T 2 ≤ 2*(1+fourierDerivativeL1 ω 1)*Real.log (2*T+2)^2 := by
  have hL := tripleBudget_height_log T hT
  have hW := fourierDerivativeL1_nonneg ω 1
  have h1 := tripleBudgetOmega_bound ω hω T hT 1
  have h2 := tripleBudgetOmega_bound ω hω T hT 2
  norm_num at h1 h2
  constructor <;> nlinarith

theorem tripleBudget_coefficient_log_height (T x : ℝ) (hT : 3≤T) (hx : 1≤x) (hxT : x≤T) :
    0≤Real.log (2*x) ∧ Real.log (2*x)≤Real.log (2*T+2) :=
  ⟨Real.log_nonneg (by linarith),Real.log_le_log (by positivity) (by linarith)⟩

theorem tripleBudget_mixed_log_height (T x y : ℝ) (hT : 3≤T)
    (hx : 1≤x) (hy : 1≤y) (hxT : x≤T) (hyT : y≤T) :
    Real.sqrt (Real.log (2*x)^3*Real.log (2*y)^3)≤Real.log (2*T+2)^3 := by
  obtain ⟨hx0,hxl⟩ := tripleBudget_coefficient_log_height T x hT hx hxT
  obtain ⟨hy0,hyl⟩ := tripleBudget_coefficient_log_height T y hT hy hyT
  have hL := tripleBudget_height_log T hT
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hh := mul_le_mul (pow_le_pow_left₀ hx0 hxl 3) (pow_le_pow_left₀ hy0 hyl 3)
    (pow_nonneg hy0 3) (pow_nonneg (by linarith) 3)
  nlinarith

theorem tripleBudget_mass_pair_height (T X Y : ℝ) (hT : 3≤T)
    (hX : 1≤X) (hY : 1≤Y) (hXT : X≤T) (hYT : Y≤T) :
    triplePrimeMass X*triplePrimeMass Y/(X*Y) ≤ triplePrimeMassConstant^2*Real.log (2*T+2)^2 := by
  have hc := triplePrimeMassConstant_pos.le
  have hL := tripleBudget_height_log T hT
  have hx := triplePrimeMass_bound X hX
  have hy := triplePrimeMass_bound Y hY
  have hsx : Real.sqrt X≤X := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hsy : Real.sqrt Y≤Y := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hmx : triplePrimeMass X≤triplePrimeMassConstant*X*Real.log (2*T+2) := hx.trans (by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hsx hc
    · exact (tripleBudget_coefficient_log_height T X hT hX hXT).2
    · exact (tripleBudget_coefficient_log_height T X hT hX hXT).1
    · positivity)
  have hmy : triplePrimeMass Y≤triplePrimeMassConstant*Y*Real.log (2*T+2) := hy.trans (by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hsy hc
    · exact (tripleBudget_coefficient_log_height T Y hT hY hYT).2
    · exact (tripleBudget_coefficient_log_height T Y hT hY hYT).1
    · positivity)
  apply (div_le_iff₀ (by positivity : 0<X*Y)).mpr
  have hh := mul_le_mul hmx hmy (tsum_nonneg (pairMeanPrimeCoefficient_nonneg Y hY)) (by positivity)
  nlinarith

theorem tripleBudget_single_words_height (ω : ℝ → ℝ) (hω : TripleBudgetWeight ω)
    (T X Y : ℝ) (hT : 3≤T) (hX : 1≤X) (hY : 1≤Y) :
    ‖tripleBudgetError ω T X Y .PAA‖ ≤ 5*tripleBudgetOmega ω T 2/T ∧
    ‖tripleBudgetError ω T X Y .APA‖ ≤ 5*tripleBudgetOmega ω T 2/T ∧
    ‖tripleBudgetError ω T X Y .AAP‖ ≤ 5*tripleBudgetOmega ω T 2/T := by
  have ht : 0<T := by linarith
  have hz : 1≤X*Y := by nlinarith [mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)]
  have ho : 0≤tripleBudgetOmega ω T 2 := fourierDerivativeL1_nonneg _ _
  have hsx : Real.sqrt X≤Y*(X*Y) := by
    have h := (Real.sqrt_le_left (by linarith : 0≤X)).mpr (show X≤X^2 by nlinarith)
    nlinarith [sq_nonneg (Y-1)]
  have hsy : Real.sqrt Y≤X*(X*Y) := by
    have h := (Real.sqrt_le_left (by linarith : 0≤Y)).mpr (show Y≤Y^2 by nlinarith)
    nlinarith [sq_nonneg (X-1)]
  have hsz : Real.sqrt (X*Y)≤X*Y := (Real.sqrt_le_left (by positivity)).mpr (by nlinarith)
  refine ⟨(tripleBudget_PAA_bound ω hω T X Y hT hX hY).trans ?_,
    (tripleBudget_APA_bound ω hω T X Y hT hX hY).trans ?_,
    (tripleBudget_AAP_bound ω hω T X Y hT hX hY).trans ?_⟩
  · apply (div_le_iff₀ (by positivity : 0<T*Y*(X*Y))).mpr
    have hh := mul_le_mul_of_nonneg_left hsx (by positivity : 0≤5*tripleBudgetOmega ω T 2)
    convert hh using 1 <;> field_simp <;> ring
  · apply (div_le_iff₀ (by positivity : 0<T*X*(X*Y))).mpr
    have hh := mul_le_mul_of_nonneg_left hsy (by positivity : 0≤5*tripleBudgetOmega ω T 2)
    convert hh using 1 <;> field_simp <;> ring
  · apply (div_le_iff₀ (by positivity : 0<T*X*Y)).mpr
    have hh := mul_le_mul_of_nonneg_left hsz (by positivity : 0≤5*tripleBudgetOmega ω T 2)
    convert hh using 1 <;> field_simp <;> ring

end
end HigherCorrelations
