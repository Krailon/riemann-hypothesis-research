import HigherCorrelations.PairMeanSandwich
import HigherCorrelations.PairMeanOffDiagonal

/-! PAIR-MEANVALUE-001: an unconditional mean-value bound with explicit
constants, ordered nearby pairs, and strict frequency cutoff. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Complex

theorem pairMeanWeighted_real_bound {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (hμ : Function.Injective μ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (M : ℝ → ℝ) (hM : Integrable M)
    (δ : ℝ) (hδ : 0 < δ)
    (hband : ∀ ξ : ℝ, δ ≤ |ξ| → pairMeanFourier (fun t => (M t:ℂ)) ξ = 0) :
    |(∫ t, M t*‖pairFrequencySum μ c t‖^2) - (∫ t, M t)*pairFrequencyDiagonal c| ≤
      (∫ t, ‖M t‖)*pairFrequencyNearby μ c δ := by
  have h := pairMeanWeighted_offdiag_bound μ hμ c hc (fun t => (M t:ℂ)) hM.ofReal δ hδ hband
  simpa only [pairMeanFourier_zero,← Complex.ofReal_mul, integral_complex_ofReal,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem pairMeanWeighted_square_integrable {ι : Type*} (μ : ι → ℝ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (M : ℝ → ℝ) (hM : Integrable M) :
    Integrable (fun t => M t*‖pairFrequencySum μ c t‖^2) := by
  apply hM.mul_bdd (((pairFrequencySum_continuous μ c hc).norm.pow 2).aestronglyMeasurable)
  filter_upwards [] with t
  change ‖‖pairFrequencySum μ c t‖^2‖ ≤ (∑' i, ‖c i‖)^2
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (pairFrequencySum_bound μ c hc t) 2

theorem pairMeanValue_explicit {ι : Type*} [Countable ι]
    (μ : ι → ℝ) (hμ : Function.Injective μ) (c : ι → ℂ)
    (hc : Summable (fun i => ‖c i‖)) (T δ : ℝ)
    (hT : 1 ≤ T) (hδlo : 1/(2*T) ≤ δ) (_hδhi : δ ≤ 1/2) :
    |(∫ t in (0:ℝ)..T, ‖pairFrequencySum μ c t‖^2) - T*pairFrequencyDiagonal c| ≤
      512/δ*pairFrequencyDiagonal c+1025*T*pairFrequencyNearby μ c δ := by
  have hT0 : 0 < T := by linarith
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδlo
  have hδT : 1 ≤ δ*(2*T) := (div_le_iff₀ (by positivity : 0 < 2*T)).mp hδlo
  have hsize : T+512/δ ≤ 1025*T := by
    have hh : 512/δ ≤ 1024*T := (div_le_iff₀ hδ).mpr (by nlinarith only [hδT])
    linarith
  have hQ : 0 ≤ pairFrequencyNearby μ c δ := by
    apply tsum_nonneg
    intro p
    split_ifs <;> positivity
  have hb (ε : ℝ) (hε : |ε| ≤ 1) :
      |(∫ t, pairMeanEnvelope T δ ε t*‖pairFrequencySum μ c t‖^2) -
        (T+ε*512/δ)*pairFrequencyDiagonal c| ≤ 1025*T*pairFrequencyNearby μ c δ := by
    have h := pairMeanWeighted_real_bound μ hμ c hc (pairMeanEnvelope T δ ε)
      (pairMeanEnvelope_integrable T δ ε hδ) δ hδ
      (pairMeanEnvelope_fourier_zero T δ ε · hδ)
    rw [pairMeanEnvelope_mass T δ ε hT0.le hδ] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((pairMeanEnvelope_norm_bound T δ ε hT0.le hδ hε).trans hsize) hQ)
  have hlo := (abs_le.mp (hb (-1) (by norm_num))).1
  have hhi := (abs_le.mp (hb 1 (by norm_num))).2
  have hsharp : (∫ t, pairMeanInterval T t*‖pairFrequencySum μ c t‖^2) =
      ∫ t in (0:ℝ)..T, ‖pairFrequencySum μ c t‖^2 := by
    have he : (fun t => pairMeanInterval T t*‖pairFrequencySum μ c t‖^2) =
        (Set.Icc 0 T).indicator (fun t => ‖pairFrequencySum μ c t‖^2) := by
      funext t
      classical
      by_cases ht : t ∈ Set.Icc 0 T <;> simp [pairMeanInterval,ht]
    rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hT0.le]
  have hl : (∫ t, pairMeanEnvelope T δ (-1) t*‖pairFrequencySum μ c t‖^2) ≤
      ∫ t in (0:ℝ)..T, ‖pairFrequencySum μ c t‖^2 := by
    rw [← hsharp]
    apply integral_mono
      (pairMeanWeighted_square_integrable μ c hc _ (pairMeanEnvelope_integrable T δ (-1) hδ))
      (pairMeanWeighted_square_integrable μ c hc _ (pairMeanInterval_integrable T))
    intro t
    exact mul_le_mul_of_nonneg_right (pairMeanEnvelope_sandwich T δ t hδ).1 (sq_nonneg _)
  have hu : (∫ t in (0:ℝ)..T, ‖pairFrequencySum μ c t‖^2) ≤
      ∫ t, pairMeanEnvelope T δ 1 t*‖pairFrequencySum μ c t‖^2 := by
    rw [← hsharp]
    apply integral_mono
      (pairMeanWeighted_square_integrable μ c hc _ (pairMeanInterval_integrable T))
      (pairMeanWeighted_square_integrable μ c hc _ (pairMeanEnvelope_integrable T δ 1 hδ))
    intro t
    exact mul_le_mul_of_nonneg_right (pairMeanEnvelope_sandwich T δ t hδ).2 (sq_nonneg _)
  rw [abs_le]
  simp only [neg_mul,one_mul,neg_div] at hlo hhi
  constructor <;> nlinarith only [hlo,hhi,hl,hu]

end
end HigherCorrelations
