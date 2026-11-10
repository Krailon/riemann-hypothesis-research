import HigherCorrelations.DensityCountDefinitions
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! UNCONDITIONAL definitions. Horizontal thresholds are strict; all zero
weights are analytic multiplicities. Boundary logarithms are transported along
segments, never chosen independently on the two horizontal edges. -/
namespace HigherCorrelations
noncomputable section
open Complex MeasureTheory

structure LittlewoodRectangle (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  horizontal_lt : a < b
  vertical_lt : c < d
  analytic : AnalyticOnNhd ℂ f (Rectangle (a+c*I) (b+d*I))
  nonzero : ∀ s ∈ RectangleBorder (a+c*I) (b+d*I), f s ≠ 0

def littlewoodSegmentLog (f : ℂ → ℂ) (z v : ℂ) (t₀ : ℝ) (k : ℂ) (t : ℝ) : ℂ :=
  k + ∫ x in t₀..t, v * logDeriv f (z + x*v)

def littlewoodBottomLog (f : ℂ → ℂ) (b c : ℝ) (k : ℂ) : ℝ → ℂ :=
  littlewoodSegmentLog f (c*I) 1 b k

def littlewoodRightLog (f : ℂ → ℂ) (b c : ℝ) (k : ℂ) : ℝ → ℂ :=
  littlewoodSegmentLog f b I c k

def littlewoodTopLog (f : ℂ → ℂ) (b c d : ℝ) (k : ℂ) : ℝ → ℂ :=
  littlewoodSegmentLog f (d*I) 1 b (littlewoodRightLog f b c k d)

def littlewoodBoundary (f : ℂ → ℂ) (a b c d : ℝ) (k : ℂ) : ℝ :=
  (∫ t in c..d, Real.log ‖f (a+t*I)‖) -
  (∫ t in c..d, Real.log ‖f (b+t*I)‖) +
  (∫ x in a..b, (littlewoodTopLog f b c d k x).im -
    (littlewoodBottomLog f b c k x).im)

def littlewoodMass (f : ℂ → ℂ) (Z : Finset ℂ) (a : ℝ) : ℝ :=
  ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) * (ρ.re-a)

def littlewoodRightCount (f : ℂ → ℂ) (Z : Finset ℂ) (σ : ℝ) : ℕ := by
  classical
  exact ∑ ρ ∈ Z.filter (fun ρ => σ < ρ.re), analyticOrderNatAt f ρ

end
end HigherCorrelations
