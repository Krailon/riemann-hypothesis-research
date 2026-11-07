import HigherCorrelations.SineBenchmarkExpansion

/-! UNCONDITIONAL five-partition benchmark and distinct ordinary/factorial cumulants. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

theorem sineBenchmark_partial_fourier (j : Fin 3) (F : 𝓢(FourierPlane,ℂ)) :
    sineLinePair j sineR2 (𝓕 F) = sineComplementPair j (fun _ => 1) F-
      sinePlanePair (fun p => (pairMeanTriangle (sineLineForm j p):ℂ)) F := by
  rw [sineLine_R2_expansion,sineLine_constant_fourier,sineLine_square_fourier]

theorem sineBenchmark_distinct_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sinePlanePair (fun p => sineR3 (planeCoords p)) (𝓕 F) = F 0-
      (∑ j : Fin 3, sineComplementPair j (fun r => (pairMeanTriangle r:ℂ)) F)+
      2*sinePlanePair sineDensityPlane F := by
  rw [sineR3_pairing_expansion,sinePlane_constant_fourier,sineCycle_distribution_fourier]
  simp_rw [sinePlane_square_fourier]

theorem sineBenchmarkRow_fourier (k : TriplePattern) (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmarkRow k (𝓕 F) = sineBenchmarkFourierRow k F := by
  cases k
  · exact sineAtom_fourier F
  · exact sineBenchmark_partial_fourier 1 F
  · exact sineBenchmark_partial_fourier 0 F
  · exact sineBenchmark_partial_fourier 2 F
  · exact sineBenchmark_distinct_fourier F

theorem sineBenchmark_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark (𝓕 F) = sineBenchmarkSpectrum F := by
  rw [sineBenchmark_five,sineBenchmark_distinct_fourier,sineAtom_fourier]
  simp_rw [sineBenchmark_partial_fourier]
  rw [sineBenchmarkSpectrum,sineCumulantDensity_pairing_expansion]
  simp_rw [sineComplement_m_expansion]
  simp only [Fin.sum_univ_three]
  ring

theorem sineOrdinaryCumulant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineOrdinaryCumulant (𝓕 F) = sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F := by
  rw [sineOrdinaryCumulant,sineAtom_fourier,sineCycle_distribution_fourier,
    sineCumulantDensity_pairing_expansion]
  simp_rw [sineLine_square_fourier]

theorem sineFactorialCumulant_fourier (F : 𝓢(FourierPlane,ℂ)) :
    sineFactorialCumulant (𝓕 F) = 2*sinePlanePair sineDensityPlane F := by
  rw [sineFactorialCumulant,sineCycle_distribution_fourier]

theorem sineBenchmark_moment_cumulant (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = sinePlanePair (fun _ => 1) F+
      (∑ j : Fin 3, sineCovarianceLift j F)+sineOrdinaryCumulant F := by
  rw [sineBenchmark_five,sineR3_pairing_expansion]
  simp_rw [sineLine_R2_expansion]
  simp only [sineCovarianceLift,sineOrdinaryCumulant,Fin.sum_univ_three]
  ring

theorem sineBenchmark_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineBenchmark F := by
  classical
  obtain ⟨P,hP⟩ := sinePlane_tempered _ sineR3_continuous 6 (fun p => sineR3_bound (planeCoords p))
  choose L hL using (fun j : Fin 3 => sineLine_tempered j sineR2 sineR2_continuous 2 sineR2_bound)
  refine ⟨P+TemperedDistribution.delta 0+∑ j, L j,?_⟩
  intro F
  rw [sineBenchmark_five]
  simp [hP,hL,TemperedDistribution.delta_apply]

theorem sineOrdinaryCumulant_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineOrdinaryCumulant F := by
  classical
  obtain ⟨P,hP⟩ := sinePlane_tempered sineCyclePlane (sineCycle_continuous.comp planeCoords.continuous)
    1 (fun p => sineCycle_bound (planeCoords p))
  choose L hL using (fun j : Fin 3 => sineLine_tempered j (fun r => (pairMeanSinc r:ℂ)^2)
    ((Complex.continuous_ofReal.comp pairMeanSinc_continuous).pow 2) 1 sineSquare_bound)
  refine ⟨TemperedDistribution.delta 0-(∑ j, L j)+(2:ℂ) • P,?_⟩
  intro F
  simp [sineOrdinaryCumulant,hP,hL,TemperedDistribution.delta_apply,smul_eq_mul]

theorem sineFactorialCumulant_tempered :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineFactorialCumulant F := by
  obtain ⟨P,hP⟩ := sinePlane_tempered sineCyclePlane (sineCycle_continuous.comp planeCoords.continuous)
    1 (fun p => sineCycle_bound (planeCoords p))
  refine ⟨(2:ℂ) • P,?_⟩
  intro F
  simp [sineFactorialCumulant,hP,smul_eq_mul]

theorem sineBenchmark_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineBenchmark F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = sineBenchmarkSpectrum F := by
  rw [TemperedDistribution.fourier_apply,hD,sineBenchmark_fourier]

theorem sineOrdinaryCumulant_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineOrdinaryCumulant F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = sinePlanePair (fun p => (sineCumulantDensity (planeCoords p):ℂ)) F := by
  rw [TemperedDistribution.fourier_apply,hD,sineOrdinaryCumulant_fourier]

theorem sineFactorialCumulant_distribution_fourier (D : 𝓢'(FourierPlane,ℂ))
    (hD : ∀ F, D F = sineFactorialCumulant F) (F : 𝓢(FourierPlane,ℂ)) :
    (𝓕 D) F = 2*sinePlanePair sineDensityPlane F := by
  rw [TemperedDistribution.fourier_apply,hD,sineFactorialCumulant_fourier]

theorem sineBenchmark_integrable (F : 𝓢(FourierPlane,ℂ)) :
    Integrable (fun p => F p*sineR3 (planeCoords p)) ∧
      ∀ j : Fin 3, Integrable (fun r => F (sineLine j r)*sineR2 r) := by
  exact ⟨sinePlane_weighted_integrable _ sineR3_continuous 6 (fun p => sineR3_bound _) F,
    fun j => sineLine_weighted_integrable j sineR2 sineR2_continuous 2 sineR2_bound F⟩

theorem sineBenchmark_continuous : Continuous sineBenchmark := by
  obtain ⟨D,hD⟩ := sineBenchmark_tempered
  have h : (D : 𝓢(FourierPlane,ℂ) → ℂ) = sineBenchmark := funext hD
  rw [← h]
  exact D.continuous

theorem sineOrdinaryCumulant_continuous : Continuous sineOrdinaryCumulant := by
  obtain ⟨D,hD⟩ := sineOrdinaryCumulant_tempered
  have h : (D : 𝓢(FourierPlane,ℂ) → ℂ) = sineOrdinaryCumulant := funext hD
  rw [← h]
  exact D.continuous

theorem sineFactorialCumulant_continuous : Continuous sineFactorialCumulant := by
  obtain ⟨D,hD⟩ := sineFactorialCumulant_tempered
  have h : (D : 𝓢(FourierPlane,ℂ) → ℂ) = sineFactorialCumulant := funext hD
  rw [← h]
  exact D.continuous

theorem sineBenchmarkRow_tempered (k : TriplePattern) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineBenchmarkRow k F := by
  cases k
  · exact ⟨TemperedDistribution.delta 0, fun F => rfl⟩
  · exact sineLine_tempered 1 sineR2 sineR2_continuous 2 sineR2_bound
  · exact sineLine_tempered 0 sineR2 sineR2_continuous 2 sineR2_bound
  · exact sineLine_tempered 2 sineR2 sineR2_continuous 2 sineR2_bound
  · exact sinePlane_tempered _ sineR3_continuous 6 (fun p => sineR3_bound (planeCoords p))

theorem sineCovarianceLift_tempered (j : Fin 3) :
    ∃ D : 𝓢'(FourierPlane,ℂ), ∀ F, D F = sineCovarianceLift j F := by
  obtain ⟨L,hL⟩ := sineLine_tempered j (fun _ => 1) continuous_const 1 (fun _ => by simp)
  obtain ⟨P,hP⟩ := sinePlane_tempered (fun p => (pairMeanSinc (sineDifferenceForm j p):ℂ)^2)
    ((Complex.continuous_ofReal.comp (pairMeanSinc_continuous.comp (sineDifferenceForm_continuous j))).pow 2)
    1 (fun p => sineSquare_bound _)
  refine ⟨L-P,?_⟩
  intro F
  simp [sineCovarianceLift,hL,hP]

theorem sineBenchmark_distribution_moment_cumulant
    (M O : 𝓢'(FourierPlane,ℂ)) (C : Fin 3 → 𝓢'(FourierPlane,ℂ))
    (hM : ∀ F, M F = sineBenchmark F) (hO : ∀ F, O F = sineOrdinaryCumulant F)
    (hC : ∀ j F, C j F = sineCovarianceLift j F) :
    M = (volume : Measure FourierPlane).toTemperedDistribution + (∑ j, C j) + O := by
  ext F
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    Measure.toTemperedDistribution_apply,hM,hO,hC]
  simpa only [sinePlanePair,mul_one] using sineBenchmark_moment_cumulant F

theorem sineBenchmark_manuscript (F : 𝓢(FourierPlane,ℂ)) :
    sineBenchmark F = (∫ p, F p*sineR3 (planeCoords p))+F 0+
      ∫ r, sineR2 r*(F (sineLine 1 r)+F (sineLine 0 r)+F (sineLine 2 r)) := by
  have hi := (sineBenchmark_integrable F).2
  have h := integral_add ((hi 1).add (hi 0)) (hi 2)
  have h10 := integral_add (hi 1) (hi 0)
  simp only [Pi.add_apply] at h h10
  rw [h10] at h
  rw [sineBenchmark_five]
  simp only [Fin.sum_univ_three,sinePlanePair,sineLinePair]
  have he : (fun r => sineR2 r*(F (sineLine 1 r)+F (sineLine 0 r)+F (sineLine 2 r))) =
      fun r => F (sineLine 1 r)*sineR2 r+F (sineLine 0 r)*sineR2 r+F (sineLine 2 r)*sineR2 r := by
    funext r; ring
  rw [he,h]
  ring

end
end HigherCorrelations
