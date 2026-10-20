import HigherCorrelations.PairZeroNorm

/-! UNCONDITIONAL exact zero-side decomposition. The quantitative bounds on the
three separately named errors are not asserted here. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

theorem pairZero_errors_integrable (X T Z : ℝ) (hX : 1 ≤ X) :
    IntervalIntegrable (fun t => ‖pairZeroFullVector X t‖^2-‖pairZeroCutoffVector X Z t‖^2) volume 0 T ∧
    IntervalIntegrable (fun t => ‖pairZeroCutoffVector X Z t‖^2-‖pairZeroWindowVector X T t‖^2) volume 0 T ∧
    IntegrableOn (fun t => ‖pairZeroWindowVector X T t‖^2) (Set.Icc (0:ℝ) T)ᶜ := by
  exact ⟨(((pairZeroFullVector_continuous X hX).norm.pow 2).sub
      ((pairZeroCutoffVector_continuous X Z).norm.pow 2)).intervalIntegrable 0 T,
    (((pairZeroCutoffVector_continuous X Z).norm.pow 2).sub
      ((pairZeroWindowVector_continuous X T).norm.pow 2)).intervalIntegrable 0 T,
    (pairZeroWindow_square_integrable X T).integrableOn⟩

theorem pairZero_norm_normalization (X T : ℝ) (hX : 0 < X) :
    2*Real.pi*(pairCorrelationSum X T).re = 4*∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2 := by
  rw [pairCorrelationSum_norm X T hX]
  simp only [Complex.ofReal_re]
  field_simp
  <;> ring

theorem pairZero_window_integral_split (X T : ℝ) (hT : 0 ≤ T) :
    (∫ t : ℝ, ‖pairZeroWindowVector X T t‖^2) =
      (∫ t in (0:ℝ)..T, ‖pairZeroWindowVector X T t‖^2) +
      ∫ t in (Set.Icc (0:ℝ) T)ᶜ, ‖pairZeroWindowVector X T t‖^2 := by
  have h := integral_add_compl (s := Set.Icc (0:ℝ) T) measurableSet_Icc (pairZeroWindow_square_integrable X T)
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT] at h
  exact h.symm

theorem pairZeroExtensionError_nonpos (X T : ℝ) : pairZeroExtensionError X T ≤ 0 := by
  unfold pairZeroExtensionError
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (integral_nonneg (fun t => sq_nonneg _))

theorem pairZero_decomposition (X T Z : ℝ) (hX : 1 ≤ X) (hT : 0 ≤ T) (_hZ : 0 ≤ Z) :
    pairZeroMeanSquare X T = 2*Real.pi*(pairCorrelationSum X T).re +
      pairZeroTruncError X T Z + pairZeroHeightError X T Z + pairZeroExtensionError X T := by
  rw [pairZeroMeanSquare_eq_full X T hX,pairZero_norm_normalization X T (by linarith)]
  unfold pairZeroTruncError pairZeroHeightError pairZeroExtensionError
  have hu : IntervalIntegrable (fun t => ‖pairZeroFullVector X t‖^2) volume 0 T :=
    ((pairZeroFullVector_continuous X hX).norm.pow 2).intervalIntegrable 0 T
  have hz : IntervalIntegrable (fun t => ‖pairZeroCutoffVector X Z t‖^2) volume 0 T :=
    ((pairZeroCutoffVector_continuous X Z).norm.pow 2).intervalIntegrable 0 T
  have hv : IntervalIntegrable (fun t => ‖pairZeroWindowVector X T t‖^2) volume 0 T :=
    ((pairZeroWindowVector_continuous X T).norm.pow 2).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub hu hz,intervalIntegral.integral_sub hz hv,
    pairZero_window_integral_split X T hT]
  ring

theorem pairZero_decomposition_manuscript (X T Z : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) (hZ : 2*T ≤ Z) :
    pairZeroMeanSquare X T = 2*Real.pi*(pairCorrelationSum X T).re +
      pairZeroTruncError X T Z + pairZeroHeightError X T Z + pairZeroExtensionError X T :=
  pairZero_decomposition X T Z hX (by linarith) (by linarith)

theorem pairZero_decomposition_unit (T Z : ℝ) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    pairZeroMeanSquare 1 T = 2*Real.pi*(pairCorrelationSum 1 T).re +
      pairZeroTruncError 1 T Z + pairZeroHeightError 1 T Z + pairZeroExtensionError 1 T :=
  pairZero_decomposition 1 T Z le_rfl hT hZ

theorem pairZero_empty_window (X T : ℝ) (h : occurrenceWindow 0 T = ∅) :
    pairZeroWindowVector X T = 0 ∧ pairCorrelationSum X T = 0 ∧ pairZeroExtensionError X T = 0 := by
  have hv : pairZeroWindowVector X T = 0 := by funext t; simp [pairZeroWindowVector,h]
  exact ⟨hv,by simp [pairCorrelationSum,h],by simp [pairZeroExtensionError,hv]⟩

theorem pairZero_height_zero (X Z : ℝ) :
    pairZeroMeanSquare X 0 = 0 ∧ pairCorrelationSum X 0 = 0 ∧
    pairZeroTruncError X 0 Z = 0 ∧ pairZeroHeightError X 0 Z = 0 ∧ pairZeroExtensionError X 0 = 0 := by
  have h := pairZero_empty_window X 0 (occurrenceWindow_empty 0 0 le_rfl)
  simp [pairZeroMeanSquare,pairZeroTruncError,pairZeroHeightError,h.2.1,h.2.2]

end
end HigherCorrelations
