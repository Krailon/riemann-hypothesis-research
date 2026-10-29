import HigherCorrelations.TripleTestDefinitions
import HigherCorrelations.TripleRetainedDefinitions

/-! UNCONDITIONAL closed-quadrant definitions. Boundary values of the ambient
smooth test specify its traces. The zero extension is only measurable. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory Set

def tripleQuadrant : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2}
def tripleQuadrantMargin (κ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1+p.2 ≤ 1-κ}
def tripleQuadrantAmplitude (ψ : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  tripleQuadrant.indicator ψ

def tripleQuadrantFourier (ψ : ℝ × ℝ → ℂ) := complexFourier (tripleQuadrantAmplitude ψ)
def tripleQuadrantStatistic (ω : ℝ → ℝ) (ψ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  tripleTestStatistic ω (tripleQuadrantAmplitude ψ) T / (Real.log T : ℂ)
def tripleQuadrantLimit (ψ : ℝ × ℝ → ℂ) : ℂ :=
  ψ (0,0)/4 + (3/4:ℂ)*∫ r : ℝ in Ioi 0, (r:ℂ)*(ψ (r,0)+ψ (0,r))
def tripleQuadrantRemainder (ω : ℝ → ℝ) (T X Y : ℝ) : ℂ :=
  tripleMasterObservable ω T X Y - (tripleRetainedMain ω T X Y : ℂ)

end
end HigherCorrelations
