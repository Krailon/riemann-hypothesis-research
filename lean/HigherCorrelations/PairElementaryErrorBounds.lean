import HigherCorrelations.PairErrorDefinitions
import HigherCorrelations.PairEulerSeries
import HigherCorrelations.PairTrivialCorrection

/-! UNCONDITIONAL Dirichlet-series and pole estimates, uniform for X≥1 and t∈ℝ. -/
namespace HigherCorrelations
noncomputable section

theorem pairDSConstant_summable : Summable (fun n : ℕ =>
    ArithmeticFunction.vonMangoldt (n+1) / (n+1 : ℝ)^(3/2 : ℝ)) := by
  simpa only [pairEulerTerm_norm, Complex.ofReal_re] using
    (pairEulerTerm_summable (3/2 : ℝ) (by norm_num)).norm

theorem pairDSConstant_nonneg : 0 ≤ pairDSConstant :=
  tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem pairDSError_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairDSError (X,t)‖ ≤ pairDSConstant / X := by
  have hz : 1 < (2-pairSpectralPoint t).re := by simp [pairSpectralPoint]; norm_num
  have hn : ‖deriv riemannZeta (2-pairSpectralPoint t) /
      riemannZeta (2-pairSpectralPoint t)‖ ≤ pairDSConstant := by
    have h := norm_tsum_le_tsum_norm (pairEulerTerm_summable _ hz).norm
    rw [pairEulerSeries _ hz] at h
    norm_num [pairEulerTerm_norm, pairSpectralPoint, pairDSConstant, neg_div] at h ⊢
    exact h
  unfold pairDSError
  simp only [norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : 0 < X)]
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (by linarith))

theorem pairPole_denominator_lower (t : ℝ) :
    (1+t^2)/2 ≤ ‖pairSpectralPoint t * (2-pairSpectralPoint t)‖ := by
  have hs : ((1+t^2)/2)^2 ≤ ‖pairSpectralPoint t * (2-pairSpectralPoint t)‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_mul]
    simp [Complex.normSq_apply, pairSpectralPoint]
    nlinarith [sq_nonneg t, sq_nonneg (t^2)]
  nlinarith [norm_nonneg (pairSpectralPoint t * (2-pairSpectralPoint t)), sq_nonneg t]

theorem pairPoleCorrection_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairPoleCorrection (X,t)‖ ≤ 4 * X^(1/2 : ℝ) / (1+t^2) := by
  have hnum : ‖Complex.exp ((Real.log X : ℂ) * (1-pairSpectralPoint t))‖ =
      X^(1/2 : ℝ) := by
    rw [Complex.norm_exp, Real.rpow_def_of_pos (by linarith : 0 < X)]
    congr 1
    norm_num [pairSpectralPoint]
  unfold pairPoleCorrection
  dsimp only [Prod.fst, Prod.snd]
  rw [norm_div, norm_mul, Complex.norm_ofNat, hnum]
  calc
    _ ≤ 2 * X^(1/2 : ℝ) / ((1+t^2)/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pairPole_denominator_lower t)
    _ = _ := by field_simp <;> ring

end
end HigherCorrelations
