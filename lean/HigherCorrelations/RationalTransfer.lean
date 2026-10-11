import HigherCorrelations.RationalTransferConvergence

/-! UNCONDITIONAL exact normalization of the rationally defined statistic.
All limits here remove zero cutoffs at fixed T. -/
namespace HigherCorrelations
noncomputable section
open scoped ContDiff

theorem transfer_log_pos (T : ℝ) (hT : 2 * Real.pi < T) :
    0 < Real.log T ∧ 0 < Real.log (T / (2 * Real.pi)) := by
  constructor
  · apply Real.log_pos
    linarith [Real.pi_gt_three]
  · apply Real.log_pos
    exact (one_lt_div (by positivity)).mpr hT

theorem transferRatio_ne_zero (T : ℝ) (hT : 2 * Real.pi < T) : transferRatio T ≠ 0 := by
  unfold transferRatio
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).2.ne')
    (Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).1.ne')

theorem transfer_normalization (T : ℝ) (hT : 2 * Real.pi < T) :
    transferCoefficient T * kernelBenchmark = transferRatio T * ordinateCoefficient T := by
  have ht : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [Real.pi_pos])
  have hb : (Real.log (T / (2 * Real.pi)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).2.ne'
  have hq : (Real.log T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).1.ne'
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold transferCoefficient kernelBenchmark transferRatio ordinateCoefficient meanSpacing
  push_cast
  field_simp [ht, hb, hq, hp]
  ring

theorem actual_rational_transfer (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    rationalTransferSum T w φ .weighted =
      transferRatio T * rationalTransferSum T w φ .ordinate +
      rationalTransferSum T w φ .arguments + rationalTransferSum T w φ .horizontal +
      rationalTransferSum T w φ .gaps := by
  simp only [rationalTransferSum, reduceCtorEq, reduceIte]
  rw [rationalTransfer_tsum_telescope T _ (meanSpacing_pos T hT) w hw φ hφ hc]
  have hn := transfer_normalization T hT
  linear_combination hn * (∑' t, rationalTransferTerm (meanSpacing T) w φ .ordinate t)

theorem actual_rational_transfer_benchmark (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ γ, γ ∉ Set.Icc T (2*T) → w γ = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (S : ℂ) :
    rationalTransferSum T w φ .ordinate - S =
      ((Real.log T : ℂ) / Real.log (T / (2 * Real.pi))) *
        (rationalTransferSum T w φ .weighted - S - rationalTransferSum T w φ .arguments -
          rationalTransferSum T w φ .horizontal - rationalTransferSum T w φ .gaps) +
      (((Real.log T : ℂ) / Real.log (T / (2 * Real.pi))) - 1) * S := by
  have hn := actual_rational_transfer T hT w hw φ hφ hc
  have hb : (Real.log (T / (2 * Real.pi)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).2.ne'
  have hq : (Real.log T : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (transfer_log_pos T hT).1.ne'
  rw [hn]
  unfold transferRatio
  field_simp [hb, hq]
  ring

theorem actual_rational_transfer_scaled_anchor (T : ℝ) (hT : 2 * Real.pi < T) (w : ℝ → ℂ)
    (hw : ∀ x, x ∉ Set.Ioo (1 : ℝ) 2 → w x = 0)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    rationalTransferSum T (scaledAnchorWeight T w) φ .weighted =
      transferRatio T * rationalTransferSum T (scaledAnchorWeight T w) φ .ordinate +
      rationalTransferSum T (scaledAnchorWeight T w) φ .arguments +
      rationalTransferSum T (scaledAnchorWeight T w) φ .horizontal +
      rationalTransferSum T (scaledAnchorWeight T w) φ .gaps :=
  actual_rational_transfer T hT _
    (scaledAnchorWeight_support T (by linarith [Real.pi_pos]) w hw) φ hφ hc

theorem rationalTransferTerm_zero_test (a : ℝ) (w : ℝ → ℂ) (k : TransferTermKind)
    (t : Fin 3 → ZeroOccurrence) : rationalTransferTerm a w (fun _ => 0) k t = 0 := by
  cases k <;> simp [rationalTransferTerm, actualCorrelationTerm, complexFourier]

theorem rationalTransferSum_zero_test (T : ℝ) (w : ℝ → ℂ) (k : TransferTermKind) :
    rationalTransferSum T w (fun _ => 0) k = 0 := by
  simp [rationalTransferSum, rationalTransferTerm_zero_test]

end
end HigherCorrelations
