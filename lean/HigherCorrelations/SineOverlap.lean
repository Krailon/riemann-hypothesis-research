import HigherCorrelations.SineOverlapDefinitions
import HigherCorrelations.SignedSectorGeometry

/-! UNCONDITIONAL interval-overlap geometry underlying TRIPLE-SINE-MEASURE-001.
This module proves no Fourier-transform or zeta-correlation assertion. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory

theorem sineOverlap_translated (ξ η : ℝ) :
    sineOverlap ξ η = sineInterval ∩ ((fun d : ℝ => ξ+d) '' sineInterval) ∩
      ((fun d : ℝ => -η+d) '' sineInterval) := by
  have shift (a : ℝ) : (fun d : ℝ => a+d) '' sineInterval = Icc (a-1/2) (a+1/2) := by
    ext d
    simp only [mem_image, sineInterval, mem_Icc]
    constructor
    · rintro ⟨x, ⟨hx,hy⟩,rfl⟩; constructor <;> linarith
    · rintro ⟨hx,hy⟩
      exact ⟨d-a, ⟨by linarith,by linarith⟩, by ring⟩
  rw [shift,shift]
  rfl

theorem sineOverlap_interval (ξ η : ℝ) :
    sineOverlap ξ η = Icc (max (max 0 ξ) (-η)-1/2)
      (min (min 0 ξ) (-η)+1/2) := by
  ext d
  simp only [sineOverlap,sineInterval,mem_inter_iff,mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1,h2⟩,h3,h4⟩,h5,h6⟩
    constructor
    · have : max (max 0 ξ) (-η) ≤ d+1/2 := by
        simp only [max_le_iff]; exact ⟨⟨by linarith,by linarith⟩,by linarith⟩
      linarith
    · have : d-1/2 ≤ min (min 0 ξ) (-η) := by
        simp only [le_min_iff]; exact ⟨⟨by linarith,by linarith⟩,by linarith⟩
      linarith
  · rintro ⟨hl,hu⟩
    have hl' : max (max 0 ξ) (-η) ≤ d+1/2 := by linarith
    have hu' : d-1/2 ≤ min (min 0 ξ) (-η) := by linarith
    simp only [max_le_iff,le_min_iff] at hl' hu'
    exact ⟨⟨⟨by linarith [hl'.1.1],by linarith [hu'.1.1]⟩,
      by linarith [hl'.1.2],by linarith [hu'.1.2]⟩,
      by linarith [hl'.2],by linarith [hu'.2]⟩

set_option maxHeartbeats 800000 in
theorem sineOverlap_span (ξ η : ℝ) :
    max (max 0 ξ) (-η)-min (min 0 ξ) (-η) = signedGauge (ξ,η) := by
  rw [signedGauge_half_sum]
  simp only [abs_eq_max_neg,max_def,min_def]
  split_ifs <;> linarith

theorem sineOverlap_volume (ξ η : ℝ) :
    volume (sineOverlap ξ η) = ENNReal.ofReal (1-signedGauge (ξ,η)) := by
  rw [sineOverlap_interval,Real.volume_Icc,← sineOverlap_span]
  congr 1
  ring

theorem sineOverlap_length (ξ η : ℝ) :
    sineOverlapLength ξ η = sineCycleDensity ξ η := by
  simp [sineOverlapLength,sineOverlap_volume,sineCycleDensity,ENNReal.toReal_ofReal',max_comm]

theorem sineOverlap_measurable (ξ η : ℝ) : MeasurableSet (sineOverlap ξ η) := by
  rw [sineOverlap_interval]
  exact measurableSet_Icc

theorem sineOverlap_finite (ξ η : ℝ) : volume (sineOverlap ξ η) < ⊤ := by
  rw [sineOverlap_volume]
  exact ENNReal.ofReal_lt_top

theorem sineOverlapIntegrand_indicator (ξ η : ℝ) :
    sineOverlapIntegrand ξ η = (sineOverlap ξ η).indicator (fun _ => (1:ℝ)) := by
  funext d
  have hx : ξ-d ∈ sineInterval ↔ d ∈ Icc (ξ-1/2) (ξ+1/2) := by
    simp only [sineInterval,mem_Icc]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hy : η+d ∈ sineInterval ↔ d ∈ Icc (-η-1/2) (-η+1/2) := by
    simp only [sineInterval,mem_Icc]; constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  classical
  by_cases h0 : d ∈ sineInterval <;> by_cases h1 : ξ-d ∈ sineInterval <;>
    by_cases h2 : η+d ∈ sineInterval <;>
    simp_all [sineOverlapIntegrand,sineOverlap,Set.indicator]

theorem sineOverlapIntegrand_integrable (ξ η : ℝ) : Integrable (sineOverlapIntegrand ξ η) := by
  rw [sineOverlapIntegrand_indicator,integrable_indicator_iff (sineOverlap_measurable ξ η)]
  exact integrableOn_const (sineOverlap_finite ξ η).ne

theorem sineOverlap_integral (ξ η : ℝ) :
    (∫ d : ℝ, sineOverlapIntegrand ξ η d) = sineCycleDensity ξ η := by
  rw [sineOverlapIntegrand_indicator,integral_indicator_const _ (sineOverlap_measurable ξ η)]
  simp only [smul_eq_mul,mul_one]
  exact sineOverlap_length ξ η

theorem sineOverlap_nonempty (ξ η : ℝ) :
    (sineOverlap ξ η).Nonempty ↔ signedGauge (ξ,η) ≤ 1 := by
  rw [sineOverlap_interval,nonempty_Icc,← sineOverlap_span]
  constructor <;> intro h <;> linarith

theorem sineOverlap_touching (ξ η : ℝ) (h : signedGauge (ξ,η) = 1) :
    sineOverlap ξ η = {max (max 0 ξ) (-η)-1/2} := by
  rw [sineOverlap_interval]
  have hs := sineOverlap_span ξ η
  have he : min (min 0 ξ) (-η)+1/2 = max (max 0 ξ) (-η)-1/2 := by linarith
  rw [he,Icc_self]

theorem sineOverlap_empty (ξ η : ℝ) (h : 1 < signedGauge (ξ,η)) :
    sineOverlap ξ η = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rw [sineOverlap_nonempty]
  exact not_le.mpr h

theorem sineOverlap_length_pos (ξ η : ℝ) :
    0 < sineOverlapLength ξ η ↔ signedGauge (ξ,η) < 1 := by
  rw [sineOverlap_length]
  simp only [sineCycleDensity,lt_max_iff,lt_self_iff_false,false_or]
  constructor <;> intro h <;> linarith

theorem sineOverlap_length_zero (ξ η : ℝ) (h : 1 ≤ signedGauge (ξ,η)) :
    sineOverlapLength ξ η = 0 := by
  rw [sineOverlap_length,sineCycleDensity,max_eq_left (by linarith)]

theorem sineOverlap_length_sector (j : Fin 6) (p : ℝ × ℝ) (hp : p ∈ tripleQuadrant) :
    sineOverlapLength (signedSector j p).1 (signedSector j p).2 = max 0 (1-p.1-p.2) := by
  rw [sineOverlap_length,sineCycleDensity,Prod.mk.eta,signedGauge_sector j p hp]
  congr 1
  ring

theorem sineOverlap_length_axes (r : ℝ) :
    sineOverlapLength r 0 = max 0 (1-|r|) ∧
    sineOverlapLength 0 r = max 0 (1-|r|) ∧
    sineOverlapLength r (-r) = max 0 (1-|r|) := by
  simp [sineOverlap_length,sineCycleDensity,signedGauge,abs_nonneg]

theorem sineOverlap_length_origin : sineOverlapLength 0 0 = 1 := by
  norm_num [sineOverlap_length,sineCycleDensity,signedGauge]

theorem sineOverlap_length_repeated (r : ℝ) :
    sineOverlapLength r (-r) = max 0 (1-|r|) := (sineOverlap_length_axes r).2.2

theorem sineOverlap_length_examples :
    sineOverlapLength (1/4) (1/4) = 1/2 ∧
    sineOverlapLength (3/4) (3/4) = 0 ∧
    sineOverlapLength 1 0 = 0 := by
  norm_num [sineOverlap_length,sineCycleDensity,signedGauge]

end
end HigherCorrelations
