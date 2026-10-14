import HigherCorrelations.PairLeftGammaBounds
import HigherCorrelations.PairZetaLogDerivative
import HigherCorrelations.PairEulerSeries

/-! Uniform logarithmic-derivative bound on odd negative vertical lines. UNCONDITIONAL.
The ordinate zero is excluded here; removing one point is harmless for Lebesgue integration. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairZeta_logDeriv_right_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 2 ≤ z.re →
    ‖-deriv riemannZeta z / riemannZeta z‖ ≤ C := by
  let C := ∑' n, ‖pairEulerTerm n 2‖
  refine ⟨C,tsum_nonneg (fun _ => norm_nonneg _),fun z hz => ?_⟩
  rw [← pairEulerSeries z (by linarith)]
  apply (norm_tsum_le_tsum_norm (pairEulerTerm_summable z (by linarith)).norm).trans
  apply Summable.tsum_le_tsum _ (pairEulerTerm_summable z (by linarith)).norm
    (pairEulerTerm_summable 2 (by norm_num)).norm
  intro n
  rw [pairEulerTerm_eq_LSeries, pairEulerTerm_eq_LSeries]
  exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz) _

theorem pairZeta_left_majorant : ∃ C G : ℝ, 0 < C ∧ 0 < G ∧ ∀ (M : ℕ) (v : ℝ),
    v ≠ 0 →
      ‖-deriv riemannZeta (-(2*(M:ℂ)+1)+(v:ℂ)*I) /
        riemannZeta (-(2*(M:ℂ)+1)+(v:ℂ)*I)‖ ≤
          C + G*Real.log (|v|+2) + 2*M := by
  obtain ⟨D,hD,hright⟩ := pairZeta_logDeriv_right_bound
  obtain ⟨G,hG,hgamma⟩ := pairDigamma_left_uniform
  refine ⟨D+|Real.log Real.pi|+1,G/2,by positivity,by positivity,fun M v hv => ?_⟩
  let z : ℂ := -(2*(M:ℂ)+1)+(v:ℂ)*I
  have hz : z.im ≠ 0 := by simpa [z] using hv
  have hr : 2 ≤ (1-z).re := by
    have := Nat.cast_nonneg (α:=ℝ) M
    simp [z]; linarith
  have hζ : riemannZeta z ≠ 0 := Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
    (by have := Nat.cast_nonneg (α:=ℝ) M; simp [z]; linarith) hz
  have hζr : riemannZeta (1-z) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  change ‖-deriv riemannZeta z / riemannZeta z‖ ≤ _
  rw [pairZeta_logDeriv_functional_eq z hz hζ hζr]
  have hb := hright (1-z) hr
  simp only [neg_div, norm_neg] at hb
  have hg := hgamma M v
  change ‖digamma (z/2)‖ + ‖digamma ((1-z)/2)‖ ≤ _ at hg
  have hn := norm_add_le (deriv riemannZeta (1-z)/riemannZeta (1-z)-(Real.log Real.pi:ℂ))
    ((1/2:ℂ)*(digamma (z/2)+digamma ((1-z)/2)))
  have hn' := norm_sub_le (deriv riemannZeta (1-z)/riemannZeta (1-z)) (Real.log Real.pi:ℂ)
  have hn'' := norm_add_le (digamma (z/2)) (digamma ((1-z)/2))
  norm_num only [norm_mul, norm_div, norm_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs] at hn hn' hb
  have hM := Nat.cast_nonneg (α:=ℝ) M
  linarith

end
end HigherCorrelations
