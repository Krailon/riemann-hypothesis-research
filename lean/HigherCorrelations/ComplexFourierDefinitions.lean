import HigherCorrelations.ZeroOccurrenceDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Project Fourier conventions, including genuinely complex arguments. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open MeasureTheory

def complexFourier (φ : ℝ × ℝ → ℂ) (z : ℂ × ℂ) : ℂ :=
  ∫ ξ : ℝ × ℝ, φ ξ * Complex.exp (2 * Real.pi * Complex.I * (z.1 * ξ.1 + z.2 * ξ.2))

def complexPair (x y : ℝ × ℝ) : ℂ × ℂ :=
  ((x.1 : ℂ) - Complex.I * y.1, (x.2 : ℂ) - Complex.I * y.2)

abbrev FourierPlane := WithLp 2 (ℝ × ℝ)

def planeCoords : FourierPlane ≃L[ℝ] ℝ × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ


def twistedAmplitude (φ : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (ξ : FourierPlane) : ℂ :=
  φ (planeCoords ξ) * Complex.exp (2 * Real.pi *
    ((y.1 : ℂ) * (planeCoords ξ).1 + (y.2 : ℂ) * (planeCoords ξ).2))


end
end HigherCorrelations
