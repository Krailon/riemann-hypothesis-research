import HigherCorrelations.PairMeanFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! UNCONDITIONAL countable double-series identity against an L1 weight.
Every interchange has the explicit L1 product majorant. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanWeightedTerm_integrable (M : ℝ → ℂ) (hM : Integrable M)
    (a : ℂ) (ν : ℝ) : Integrable (fun t => M t*(a*pairMeanCharacter (ν*t))) := by
  apply (hM.norm.mul_const ‖a‖).mono'
    (hM.aestronglyMeasurable.mul ((continuous_const.mul
      (pairMeanCharacter_continuous.comp (by fun_prop))).aestronglyMeasurable))
  filter_upwards [] with t
  simp [pairMeanCharacter_norm]

theorem pairMeanWeightedTerm_integral (M : ℝ → ℂ) (a : ℂ) (ν : ℝ) :
    (∫ t, M t*(a*pairMeanCharacter (ν*t))) = a*pairMeanFourier M (-ν) := by
  rw [pairMeanFourier, ← integral_const_mul]
  congr 1
  funext t
  rw [show -t* -ν = ν*t by ring]
  ring

theorem pairFrequencySum_sq_expansion {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (t : ℝ) :
    (↑(‖pairFrequencySum μ c t‖^2):ℂ) =
      ∑' p : ι × ι, c p.1*(starRingEnd ℂ) (c p.2)*pairMeanCharacter ((μ p.1-μ p.2)*t) := by
  rw [ofReal_pow, ← Complex.mul_conj']
  unfold pairFrequencySum
  rw [Complex.conj_tsum]
  have hs := pairFrequency_terms_summable μ c hc t
  have hs' : Summable (fun i => ‖(starRingEnd ℂ) (c i*pairMeanCharacter (μ i*t))‖) := by
    simpa only [Complex.norm_conj] using hs
  rw [tsum_mul_tsum_of_summable_norm hs hs']
  apply tsum_congr
  intro p
  simp only [map_mul,pairMeanCharacter_conj]
  rw [show (μ p.1-μ p.2)*t = μ p.1*t + -(μ p.2*t) by ring,pairMeanCharacter_add]
  ring

theorem pairMeanWeighted_square_identity {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (c : ι → ℂ) (hc : Summable (fun i => ‖c i‖))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∫ t, M t*(↑(‖pairFrequencySum μ c t‖^2):ℂ)) =
      ∑' p : ι × ι, c p.1*(starRingEnd ℂ) (c p.2)*pairMeanFourier M (μ p.2-μ p.1) := by
  let G : ι × ι → ℝ → ℂ := fun p t =>
    M t*(c p.1*(starRingEnd ℂ) (c p.2)*pairMeanCharacter ((μ p.1-μ p.2)*t))
  have hG (p) : Integrable (G p) := pairMeanWeightedTerm_integrable M hM _ _
  have hL1 : Summable (fun p => ∫ t, ‖G p t‖) := by
    have he (p : ι × ι) : (∫ t, ‖G p t‖) = (∫ t, ‖M t‖)*(‖c p.1‖*‖c p.2‖) := by
      simp only [G,norm_mul,Complex.norm_conj,pairMeanCharacter_norm,mul_one]
      exact integral_mul_const _ _
    simp_rw [he]
    exact (pairFrequency_product_summable c hc).mul_left _
  have hsum (t : ℝ) : Summable (fun p : ι × ι =>
      c p.1*(starRingEnd ℂ) (c p.2)*pairMeanCharacter ((μ p.1-μ p.2)*t)) := by
    apply Summable.of_norm
    simpa only [norm_mul,Complex.norm_conj,pairMeanCharacter_norm,mul_one] using
      pairFrequency_product_summable c hc
  calc
    _ = ∫ t, ∑' p, G p t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [pairFrequencySum_sq_expansion μ c hc t, tsum_mul_left]
    _ = ∑' p, ∫ t, G p t := (integral_tsum_of_summable_integral_norm hG hL1).symm
    _ = _ := by
      apply tsum_congr
      intro p
      simpa only [G,neg_sub] using pairMeanWeightedTerm_integral M (c p.1*(starRingEnd ℂ) (c p.2)) (μ p.1-μ p.2)

end
end HigherCorrelations
