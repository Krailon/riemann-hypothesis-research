import HigherCorrelations.PairAsymptoticDefinitions
import HigherCorrelations.PairZeroNorm

/-! UNCONDITIONAL finite-pair inversion and normalization. No asymptotic input. -/
namespace HigherCorrelations
noncomputable section

theorem pairCorrelationSum_inv (X T : ℝ) :
    pairCorrelationSum X⁻¹ T = pairCorrelationSum X T := by
  unfold pairCorrelationSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.log_inv]
  push_cast
  congr 1
  · congr 1; ring
  · congr 2; ring

theorem pairNormalizedCorrelation_complex (T α : ℝ) (hT : 3 ≤ T) :
    (pairNormalizedCorrelation T α : ℂ) =
      pairCorrelationSum (T^α) T / ((T*Real.log T/(2*Real.pi) : ℝ):ℂ) := by
  have ht : 0 < T := by linarith
  have hp : 0 < T^α := Real.rpow_pos_of_pos ht _
  have him := pairCorrelationSum_im (T^α) T hp
  have hz : pairCorrelationSum (T^α) T = ((pairCorrelationSum (T^α) T).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hz]
  unfold pairNormalizedCorrelation
  push_cast
  field_simp
  <;> ring

theorem pairNormalizedCorrelation_nonneg (T α : ℝ) (hT : 3 ≤ T) :
    0 ≤ pairNormalizedCorrelation T α := by
  have ht : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hp := pairCorrelationSum_re_nonneg (T^α) T (Real.rpow_pos_of_pos ht _)
  unfold pairNormalizedCorrelation
  positivity

theorem pairNormalizedCorrelation_even (T α : ℝ) (hT : 0 < T) :
    pairNormalizedCorrelation T (-α) = pairNormalizedCorrelation T α := by
  unfold pairNormalizedCorrelation
  rw [Real.rpow_neg hT.le, pairCorrelationSum_inv]

theorem pairNormalizedCorrelation_abs (T α : ℝ) (hT : 0 < T) :
    pairNormalizedCorrelation T |α| = pairNormalizedCorrelation T α := by
  rcases le_total 0 α with h|h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, pairNormalizedCorrelation_even T α hT]

end
end HigherCorrelations
