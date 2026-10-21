import HigherCorrelations.PairZeroBoundDefinitions

/-! Independent statement surface; intentional holes occur only in verification challenges. -/
namespace HigherCorrelations
noncomputable section

theorem pairZeroCutoff_admissible (T : ℝ) (hT : 5 ≤ T) :
    2*T ≤ T*Real.log T^2 := by sorry

theorem pairZeroCutoff_log (T : ℝ) (hT : 5 ≤ T) :
    0 ≤ Real.log (T*Real.log T^2) ∧
    Real.log (T*Real.log T^2) ≤ 3*Real.log T := by sorry

theorem pairZero_error_triangle (X T Z : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
      |pairZeroTruncError X T Z| + |pairZeroHeightError X T Z| +
      |pairZeroExtensionError X T| := by sorry

theorem pairZeroCutoff_errors :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T : ℝ, 1 ≤ X → 5 ≤ T →
        |pairZeroTruncError X T (T*Real.log T^2)| ≤ Ctr*X ∧
        |pairZeroHeightError X T (T*Real.log T^2)| ≤
          Ch*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 ∧
        |pairZeroExtensionError X T| ≤
          Ce*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^2 ∧
        pairZeroExtensionError X T ≤ 0 := by sorry

theorem pairZeroComparison_smallHeight :
    ∃ C : ℝ, 0 < C ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T → T ≤ 5 →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤ C*X := by sorry

theorem pairZeroComparison_optimized :
    ∃ Cb Cx : ℝ, 0 < Cb ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
        Cb*X^(2*pairZeroHorizontalEnvelope (T*Real.log T^2))*Real.log T^3 + Cx*X := by sorry

theorem pairZeroHorizontalEnvelope_strip (Z : ℝ) :
    pairZeroHorizontalEnvelope Z ≤ 3/8 := by sorry

theorem pairZeroComparison_log_absorption (T : ℝ) (hT : 1 ≤ T) :
    Real.log T^3 ≤ 384*T^(1/4:ℝ) := by sorry

theorem pairZeroComparison_weight_absorption (X T : ℝ) (hX : 1 ≤ X)
    (hXT : X ≤ T) : X^(3/4:ℝ)*Real.log T^3 ≤ 384*T := by sorry

theorem pairZeroComparison_strip_optimized :
    ∃ Cb Cx : ℝ, 0 < Cb ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤
        Cb*X^(3/4:ℝ)*Real.log T^3 + Cx*X := by sorry

theorem pairZeroComparison_uniform_errors :
    ∃ Ctr Ch Ce : ℝ, 0 < Ctr ∧ 0 < Ch ∧ 0 < Ce ∧
      ∀ X T : ℝ, 1 ≤ X → 5 ≤ T → X ≤ T →
        |pairZeroTruncError X T (T*Real.log T^2)| ≤ Ctr*X ∧
        |pairZeroHeightError X T (T*Real.log T^2)| ≤ Ch*T ∧
        |pairZeroExtensionError X T| ≤ Ce*T ∧ pairZeroExtensionError X T ≤ 0 := by sorry

theorem pairZeroComparison_uniform :
    ∃ Ct Cx : ℝ, 0 < Ct ∧ 0 < Cx ∧ ∀ X T : ℝ, 1 ≤ X → 3 ≤ T → X ≤ T →
      |pairZeroMeanSquare X T - 2*Real.pi*(pairCorrelationSum X T).re| ≤ Ct*T+Cx*X := by sorry

end
end HigherCorrelations
