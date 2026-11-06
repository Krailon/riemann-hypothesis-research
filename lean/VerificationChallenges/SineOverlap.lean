import HigherCorrelations.SineOverlapDefinitions

/-! UNCONDITIONAL independent statements. Intentional holes are confined to
verification challenges; the solution proof module is not imported. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory

theorem sineOverlap_translated (ξ η : ℝ) :
    sineOverlap ξ η = sineInterval ∩ ((fun d : ℝ => ξ+d) '' sineInterval) ∩
      ((fun d : ℝ => -η+d) '' sineInterval) := by sorry

theorem sineOverlap_interval (ξ η : ℝ) :
    sineOverlap ξ η = Icc (max (max 0 ξ) (-η)-1/2)
      (min (min 0 ξ) (-η)+1/2) := by sorry

theorem sineOverlap_span (ξ η : ℝ) :
    max (max 0 ξ) (-η)-min (min 0 ξ) (-η) = signedGauge (ξ,η) := by sorry

theorem sineOverlap_volume (ξ η : ℝ) :
    volume (sineOverlap ξ η) = ENNReal.ofReal (1-signedGauge (ξ,η)) := by sorry

theorem sineOverlap_length (ξ η : ℝ) :
    sineOverlapLength ξ η = sineCycleDensity ξ η := by sorry

theorem sineOverlap_measurable (ξ η : ℝ) : MeasurableSet (sineOverlap ξ η) := by sorry

theorem sineOverlap_finite (ξ η : ℝ) : volume (sineOverlap ξ η) < ⊤ := by sorry

theorem sineOverlapIntegrand_indicator (ξ η : ℝ) :
    sineOverlapIntegrand ξ η = (sineOverlap ξ η).indicator (fun _ => (1:ℝ)) := by sorry

theorem sineOverlapIntegrand_integrable (ξ η : ℝ) : Integrable (sineOverlapIntegrand ξ η) := by sorry

theorem sineOverlap_integral (ξ η : ℝ) :
    (∫ d : ℝ, sineOverlapIntegrand ξ η d) = sineCycleDensity ξ η := by sorry

theorem sineOverlap_nonempty (ξ η : ℝ) :
    (sineOverlap ξ η).Nonempty ↔ signedGauge (ξ,η) ≤ 1 := by sorry

theorem sineOverlap_touching (ξ η : ℝ) (h : signedGauge (ξ,η) = 1) :
    sineOverlap ξ η = {max (max 0 ξ) (-η)-1/2} := by sorry

theorem sineOverlap_empty (ξ η : ℝ) (h : 1 < signedGauge (ξ,η)) :
    sineOverlap ξ η = ∅ := by sorry

theorem sineOverlap_length_pos (ξ η : ℝ) :
    0 < sineOverlapLength ξ η ↔ signedGauge (ξ,η) < 1 := by sorry

theorem sineOverlap_length_zero (ξ η : ℝ) (h : 1 ≤ signedGauge (ξ,η)) :
    sineOverlapLength ξ η = 0 := by sorry

theorem sineOverlap_length_sector (j : Fin 6) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrant) :
    sineOverlapLength (signedSector j p).1 (signedSector j p).2 = max 0 (1-p.1-p.2) := by sorry

theorem sineOverlap_length_axes (r : ℝ) :
    sineOverlapLength r 0 = max 0 (1-|r|) ∧
    sineOverlapLength 0 r = max 0 (1-|r|) ∧
    sineOverlapLength r (-r) = max 0 (1-|r|) := by sorry

theorem sineOverlap_length_origin : sineOverlapLength 0 0 = 1 := by sorry

theorem sineOverlap_length_repeated (r : ℝ) :
    sineOverlapLength r (-r) = max 0 (1-|r|) := by sorry

theorem sineOverlap_length_examples :
    sineOverlapLength (1/4) (1/4) = 1/2 ∧
    sineOverlapLength (3/4) (3/4) = 0 ∧
    sineOverlapLength 1 0 = 0 := by sorry

end
end HigherCorrelations
