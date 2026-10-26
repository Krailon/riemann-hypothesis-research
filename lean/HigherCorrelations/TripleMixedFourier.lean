import HigherCorrelations.PairMeanIntegration
import HigherCorrelations.PairMeanFourierRules

/-! UNCONDITIONAL mixed Fourier product. The two coefficient families and
frequencies are independent; absolute coefficient masses justify every interchange. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairFrequencySum_cross_expansion {ι κ : Type*}
    (μ : ι → ℝ) (ν : κ → ℝ) (c : ι → ℂ) (d : κ → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (hd : Summable (fun j => ‖d j‖)) (t : ℝ) :
    pairFrequencySum μ c t * star (pairFrequencySum ν d t) =
      ∑' p : ι × κ, c p.1*star (d p.2)*pairMeanCharacter ((μ p.1-ν p.2)*t) := by
  unfold pairFrequencySum
  simp only [Complex.star_def]
  rw [Complex.conj_tsum]
  have hs := pairFrequency_terms_summable μ c hc t
  have hs' : Summable (fun j => ‖(starRingEnd ℂ) (d j*pairMeanCharacter (ν j*t))‖) := by
    simpa only [Complex.norm_conj] using pairFrequency_terms_summable ν d hd t
  rw [tsum_mul_tsum_of_summable_norm hs hs']
  apply tsum_congr
  intro p
  simp only [map_mul,pairMeanCharacter_conj]
  rw [show (μ p.1-ν p.2)*t = μ p.1*t + -(ν p.2*t) by ring,pairMeanCharacter_add]
  ring

theorem pairMeanWeighted_cross_identity {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : ι → ℝ) (ν : κ → ℝ) (c : ι → ℂ) (d : κ → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (hd : Summable (fun j => ‖d j‖))
    (M : ℝ → ℂ) (hM : Integrable M) :
    (∫ t, M t*(pairFrequencySum μ c t*star (pairFrequencySum ν d t))) =
      ∑' p : ι × κ, c p.1*star (d p.2)*pairMeanFourier M (ν p.2-μ p.1) := by
  let G : ι × κ → ℝ → ℂ := fun p t =>
    M t*(c p.1*star (d p.2)*pairMeanCharacter ((μ p.1-ν p.2)*t))
  have hG (p) : Integrable (G p) := pairMeanWeightedTerm_integrable M hM _ _
  have hL1 : Summable (fun p => ∫ t, ‖G p t‖) := by
    have he (p : ι × κ) : (∫ t, ‖G p t‖) = (∫ t, ‖M t‖)*(‖c p.1‖*‖d p.2‖) := by
      simp only [G,norm_mul,norm_star,pairMeanCharacter_norm,mul_one]
      exact integral_mul_const _ _
    simp_rw [he]
    exact (hc.mul_of_nonneg hd (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left _
  calc
    _ = ∫ t, ∑' p, G p t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [pairFrequencySum_cross_expansion μ ν c d hc hd t,tsum_mul_left]
    _ = ∑' p, ∫ t, G p t := (integral_tsum_of_summable_integral_norm hG hL1).symm
    _ = _ := by
      apply tsum_congr
      intro p
      simpa only [G,neg_sub] using pairMeanWeightedTerm_integral M (c p.1*star (d p.2)) (μ p.1-ν p.2)

/-- Scaling includes the normalization 1/T; no residual factor T remains. -/
theorem pairMeanFourier_normalized (φ : ℝ → ℝ) (T ξ : ℝ) (hT : 0<T) :
    pairMeanFourier (fun t => ((φ (t/T)/T:ℝ):ℂ)) ξ =
      pairMeanFourier (fun u => (φ u:ℂ)) (T*ξ) := by
  have he : (fun t => ((φ (t/T)/T:ℝ):ℂ)) =
      fun t => (1/(T:ℂ))*(φ (t/T):ℂ) := by funext t; push_cast; ring
  rw [he,pairMeanFourier_const_mul,pairMeanFourier_div (fun u => (φ u:ℂ)) T ξ hT.ne',abs_of_pos hT]
  have hn : (T:ℂ)≠0 := by exact_mod_cast hT.ne'
  field_simp

end
end HigherCorrelations
