import HigherCorrelations.SineBenchmarkDefinitions
import HigherCorrelations.SineFourierPairing

/-! UNCONDITIONAL determinant and closed-hexagon cumulant algebra. -/
namespace HigherCorrelations
noncomputable section

theorem sineR3_determinant (u v : ℝ) :
    Matrix.det !![(1:ℂ), (pairMeanSinc u:ℂ), (pairMeanSinc v:ℂ);
      (pairMeanSinc u:ℂ), 1, (pairMeanSinc (u-v):ℂ);
      (pairMeanSinc v:ℂ), (pairMeanSinc (u-v):ℂ), 1] = sineR3 (u,v) := by
  simp [Matrix.det_fin_three,sineR3,sineCycle]
  ring

theorem sineCumulantDensity_closed (p : ℝ × ℝ) (hp : signedGauge p ≤ 1) :
    sineCumulantDensity p = 0 := by
  have hx : |p.1| ≤ 1 := ((le_max_left _ _).trans (le_max_left _ _)).trans hp
  have hy : |p.2| ≤ 1 := ((le_max_right _ _).trans (le_max_left _ _)).trans hp
  have hz : |p.1+p.2| ≤ 1 := (le_max_right _ _).trans hp
  have hs := signedGauge_half_sum p
  simp only [sineCumulantDensity,pairMeanTriangle,sineCycleDensity,
    max_eq_right (sub_nonneg.mpr hx),max_eq_right (sub_nonneg.mpr hy),
    max_eq_right (sub_nonneg.mpr hz),max_eq_right (sub_nonneg.mpr hp)]
  linarith

theorem sineCumulantDensity_exterior : sineCumulantDensity (3/4,3/4) = 1/2 := by
  norm_num [sineCumulantDensity,pairMeanTriangle,sineCycleDensity,signedGauge]

theorem sineFactorialDensity_origin : 2*sineCycleDensity 0 0 = 2 := by
  norm_num [sineCycleDensity,signedGauge]

theorem sineCumulants_distinct : sineCumulantDensity (0,0) ≠ 2*sineCycleDensity 0 0 := by
  norm_num [sineCumulantDensity,pairMeanTriangle,sineCycleDensity,signedGauge]

theorem sineR3_factorial_identity (u v : ℝ) :
    sineR3 (u,v)-sineR2 u-sineR2 v-sineR2 (u-v)+2 = 2*sineCycle (u,v) := by
  simp only [sineR3,sineR2]
  ring

theorem sineFactorialDensity_positive (p : ℝ × ℝ) (hp : signedGauge p < 1) :
    0 < 2*sineCycleDensity p.1 p.2 := by
  have h : 0 < 1-signedGauge p := by linarith
  change 0 < 2*max 0 (1-signedGauge p)
  rw [max_eq_right h.le]
  positivity

end
end HigherCorrelations
