import HigherCorrelations.PairAsymptoticDefinitions
import HigherCorrelations.PairRHSMean
import HigherCorrelations.PairZeroComparison

/-! UNCONDITIONAL assembly with three actual errors and four bound scales.
The comparison uses the pinned PREPRINT strip; total constants are existential. -/
namespace HigherCorrelations
noncomputable section

theorem pairNormalized_decomposition (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T) :
    2*Real.pi*(pairCorrelationSum X T).re/(T*Real.log T) =
      Real.log T/X^2+Real.log X/Real.log T + pairNormalizedPeakError X T +
      pairNormalizedMeanError X T + pairNormalizedComparisonError X T := by
  have hz := pairRHSSquare_eq_zeroMeanSquare X T hX (by linarith)
  have he := pairRHS_decomposition X T hX (by linarith)
  have ht : T ≠ 0 := by linarith
  have hl : Real.log T ≠ 0 := ne_of_gt (by linarith [(pairRHS_log_comparison T hT).1])
  unfold pairNormalizedPeakError pairNormalizedMeanError pairNormalizedComparisonError
  rw [← hz,he]
  field_simp
  <;> ring

theorem pairNormalized_errors :
    ∃ A B D E : ℝ, 0<A ∧ 0<B ∧ 0<D ∧ 0<E ∧ ∀ X T : ℝ,
      1≤X → 3≤T → X≤T →
      |pairNormalizedPeakError X T| ≤ A/X^2 ∧
      |pairNormalizedMeanError X T| ≤ B/Real.sqrt (Real.log T) ∧
      |pairNormalizedComparisonError X T| ≤ D/Real.log T+E*X/(T*Real.log T) := by
  obtain ⟨A,hA,B,hB,h⟩ := pairRHSMean_uniform
  obtain ⟨D,E,hD,hE,hcomp⟩ := pairZeroComparison_uniform
  refine ⟨A,B,D,E,hA,hB,hD,hE,fun X T hX hT hXT => ?_⟩
  obtain ⟨_,_,ha,hb⟩ := h X T hX hT hXT
  have hc := hcomp X T hX hT hXT
  have ht : 0<T := by linarith
  have hl : 0<Real.log T := by linarith [(pairRHS_log_comparison T hT).1]
  have hs : 0<Real.sqrt (Real.log T) := Real.sqrt_pos.mpr hl
  have hs2 := Real.sq_sqrt hl.le
  have hden : 0<T*Real.log T := mul_pos ht hl
  unfold pairNormalizedPeakError pairNormalizedMeanError pairNormalizedComparisonError
  simp only [abs_div,abs_of_pos hden]
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ (A*(T*Real.log T/X^2))/(T*Real.log T) := div_le_div_of_nonneg_right ha hden.le
      _ = _ := by field_simp
  · calc
      _ ≤ (B*(T*Real.sqrt (Real.log T)))/(T*Real.log T) := div_le_div_of_nonneg_right hb hden.le
      _ = _ := by field_simp; nlinarith
  · rw [abs_sub_comm]
    calc
      _ ≤ (D*T+E*X)/(T*Real.log T) := div_le_div_of_nonneg_right hc hden.le
      _ = _ := by field_simp

theorem pairNormalized_comparison_scales (X T : ℝ) (hX : 1 ≤ X) (hT : 3 ≤ T)
    (hXT : X ≤ T) :
    X/(T*Real.log T) ≤ 1/Real.log T ∧
    1/Real.log T ≤ 1/Real.sqrt (Real.log T) := by
  have ht : 0<T := by linarith
  have hl := (pairRHS_log_comparison T hT).1
  have hl0 : 0<Real.log T := by linarith
  have hs := Real.sq_sqrt hl0.le
  have hsq := Real.sqrt_nonneg (Real.log T)
  have hsq0 : 0<Real.sqrt (Real.log T) := Real.sqrt_pos.mpr hl0
  constructor
  · apply (div_le_iff₀ (mul_pos ht hl0)).mpr
    have he : (1/Real.log T)*(T*Real.log T) = T := by field_simp
    rwa [he]
  · exact one_div_le_one_div_of_le hsq0 (by nlinarith)

theorem pairNormalized_base_bound :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧ ∀ X T : ℝ, 1≤X → 3≤T → X≤T →
      |2*Real.pi*(pairCorrelationSum X T).re/(T*Real.log T) -
        (Real.log T/X^2+Real.log X/Real.log T)| ≤ C₁/X^2+C₂/Real.sqrt (Real.log T) := by
  obtain ⟨A,B,D,E,hA,hB,hD,hE,h⟩ := pairNormalized_errors
  refine ⟨A,B+D+E,hA,by positivity,fun X T hX hT hXT => ?_⟩
  obtain ⟨ha,hb,hc⟩ := h X T hX hT hXT
  obtain ⟨hscale1,hscale2⟩ := pairNormalized_comparison_scales X T hX hT hXT
  rw [pairNormalized_decomposition X T hX hT]
  have he : Real.log T/X^2+Real.log X/Real.log T+pairNormalizedPeakError X T+
      pairNormalizedMeanError X T+pairNormalizedComparisonError X T-
      (Real.log T/X^2+Real.log X/Real.log T) =
      (pairNormalizedPeakError X T+pairNormalizedMeanError X T)+pairNormalizedComparisonError X T := by ring
  rw [he]
  have hab := (abs_add_le (pairNormalizedPeakError X T+pairNormalizedMeanError X T)
    (pairNormalizedComparisonError X T)).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hd := mul_le_mul_of_nonneg_left hscale2 hD.le
  have he' := mul_le_mul_of_nonneg_left (hscale1.trans hscale2) hE.le
  simp only [div_eq_mul_inv] at ha hb hc hd he' ⊢
  nlinarith

end
end HigherCorrelations
