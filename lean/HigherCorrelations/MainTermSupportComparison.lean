import HigherCorrelations.MainTermBenchmarkComparison

/-! UNCONDITIONAL support cancellation and the exact three trace formula. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem sineComplement_gauge (j : Fin 3) (r : ℝ) :
    signedGauge (planeCoords (sineComplement j r)) = |r| := by
  fin_cases j <;> simp [sineComplement,sineSliceMap,signedGauge,abs_nonneg]

theorem sineBenchmark_planar_zero (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) :
    sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with p
  by_cases hp : F p = 0
  · simp [hp]
  · simp only [sineCumulantDensity_closed _ (hs p hp),Complex.ofReal_zero,mul_zero,Pi.zero_apply]

theorem sineBenchmark_line_weight (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) (j : Fin 3) (r : ℝ) :
    F (sineComplement j r)*(1-(pairMeanTriangle r:ℂ)) =
      ((|r|:ℝ):ℂ)*F (sineComplement j r) := by
  by_cases hz : F (sineComplement j r) = 0
  · simp [hz]
  · have hr : |r| ≤ 1 := by simpa only [sineComplement_gauge] using hs _ hz
    rw [pairMeanTriangle,max_eq_right (sub_nonneg.mpr hr)]
    push_cast
    ring

theorem sineBenchmark_trace_integrable (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) (j : Fin 3) :
    Integrable (fun r : ℝ => ((|r|:ℝ):ℂ)*F (sineComplement j r)) := by
  simpa only [sineBenchmark_line_weight F hs] using (sineBenchmarkSpectrum_integrable F).2 j

theorem sineBenchmarkSpectrum_closed (F : 𝓢(FourierPlane,ℂ))
    (hs : ∀ p, F p ≠ 0 → signedGauge (planeCoords p) ≤ 1) :
    sineBenchmarkSpectrum F = F 0 + ∫ r : ℝ, ((|r|:ℝ):ℂ)*
      (F (planeCoords.symm (r,0))+F (planeCoords.symm (0,r))+F (planeCoords.symm (r,-r))) := by
  have h0 := sineBenchmark_trace_integrable F hs 0
  have h1 := sineBenchmark_trace_integrable F hs 1
  have h2 := sineBenchmark_trace_integrable F hs 2
  have hi := integral_add (h1.add h0) h2
  have hj := integral_add h1 h0
  simp only [Pi.add_apply] at hi hj
  rw [hj] at hi
  rw [sineBenchmarkSpectrum,sineBenchmark_planar_zero F hs,add_zero]
  simp only [sineComplementPair,sineBenchmark_line_weight F hs,Fin.sum_univ_three]
  have he : (fun r : ℝ => ((|r|:ℝ):ℂ)*(F (planeCoords.symm (r,0))+
      F (planeCoords.symm (0,r))+F (planeCoords.symm (r,-r)))) =
      fun r => ((|r|:ℝ):ℂ)*F (sineComplement 1 r)+((|r|:ℝ):ℂ)*F (sineComplement 0 r)+
        ((|r|:ℝ):ℂ)*F (sineComplement 2 r) := by
    funext r
    simp [sineComplement,sineSliceMap]
    ring
  rw [he,hi]
  ring

theorem mainTermBenchmark_closed (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p | signedGauge p ≤ 1}) :
    sineBenchmark (mainTermPhysicalTest φ hφ hc) = φ (0,0)+
      ∫ r : ℝ, ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r)) := by
  rw [mainTermPhysicalTest,sineBenchmark_inverse_pairing]
  have hh : ∀ p, mainTermFrequencyTest φ hφ hc p ≠ 0 → signedGauge (planeCoords p) ≤ 1 := by
    intro p hp
    exact hs (subset_tsupport φ hp)
  rw [sineBenchmarkSpectrum_closed _ hh]
  simp only [mainTermFrequencyTest_apply,map_zero,ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem mainTermBenchmark_margin (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hs : tsupport φ ⊆ signedMargin κ) :
    sineBenchmark (mainTermPhysicalTest φ hφ hc) = φ (0,0)+
      ∫ r : ℝ, ((|r|:ℝ):ℂ)*(φ (r,0)+φ (0,r)+φ (r,-r)) := by
  apply mainTermBenchmark_closed φ hφ hc
  intro p hp
  have hh := hs hp
  change signedGauge p ≤ 1-κ at hh
  change signedGauge p ≤ 1
  linarith

theorem mainTermComparison_exact (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {p | signedGauge p ≤ 1}) :
    signedLimit φ = (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc) := by
  rw [mainTermBenchmark_closed φ hφ hc hs,signedLimit]
  ring

theorem mainTermComparison_margin (φ : ℝ × ℝ → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hs : tsupport φ ⊆ signedMargin κ) :
    signedLimit φ = (3/2:ℂ)*sineBenchmark (mainTermPhysicalTest φ hφ hc) := by
  rw [mainTermBenchmark_margin φ hφ hc κ hκ hs,signedLimit]
  ring

end
end HigherCorrelations
