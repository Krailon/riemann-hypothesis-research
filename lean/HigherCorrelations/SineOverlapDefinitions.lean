import HigherCorrelations.SignedSectorDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! UNCONDITIONAL definitions for the sine-cycle interval geometry.
The intervals are closed; all measures use one-dimensional Lebesgue measure. -/
namespace HigherCorrelations
noncomputable section
open Set MeasureTheory

def sineInterval : Set ℝ := Icc (-(1/2 : ℝ)) (1/2)
def sineOverlap (ξ η : ℝ) : Set ℝ :=
  sineInterval ∩ Icc (ξ-1/2) (ξ+1/2) ∩ Icc (-η-1/2) (-η+1/2)
def sineOverlapLength (ξ η : ℝ) : ℝ := (volume (sineOverlap ξ η)).toReal
def sineCycleDensity (ξ η : ℝ) : ℝ := max 0 (1-signedGauge (ξ,η))
def sineOverlapIntegrand (ξ η d : ℝ) : ℝ :=
  sineInterval.indicator (fun _ => (1:ℝ)) d *
  sineInterval.indicator (fun _ => (1:ℝ)) (ξ-d) *
  sineInterval.indicator (fun _ => (1:ℝ)) (η+d)

end
end HigherCorrelations
