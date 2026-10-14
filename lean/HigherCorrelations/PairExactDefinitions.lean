import HigherCorrelations.PairSeriesDefinitions
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Definition-only interface for the exact pair explicit formula. UNCONDITIONAL.
All positive-real powers are exp(log X * z). Trivial zeros are indexed by n+1.
The full identity is a proof target, not a hypothesis or an axiom. -/
namespace HigherCorrelations
noncomputable section

def pairSpectralPoint (t : ℝ) : ℂ := 1/2 + Complex.I * t

def pairCompletedFactor (z : ℂ) : ℂ :=
  (z-1) * Complex.exp (-(z/2)*(Real.log Real.pi:ℂ)) *
    Complex.Gamma (z/2+1) * riemannZeta z

def pairContourKernel (X t : ℝ) (z : ℂ) : ℂ :=
  2 * Complex.exp ((Real.log X : ℂ) * (z - pairSpectralPoint t)) /
    ((z - pairSpectralPoint t)^2 - 1)

def pairContourIntegrand (X t : ℝ) (z : ℂ) : ℂ :=
  (-deriv riemannZeta z / riemannZeta z) * pairContourKernel X t z

def pairEulerTerm (n : ℕ) (z : ℂ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
    Complex.exp ((Real.log (n+1 : ℝ) : ℂ) * (-z))

def pairRightIntegral (p : ℝ × ℝ) : ℂ :=
  (1 / (2*(Real.pi:ℂ))) * ∫ v : ℝ,
    pairContourIntegrand p.1 p.2 (5/2+(v:ℂ)*Complex.I)

def pairPoleCorrection (p : ℝ × ℝ) : ℂ :=
  2 * Complex.exp ((Real.log p.1 : ℂ) * (1 - pairSpectralPoint p.2)) /
    (pairSpectralPoint p.2 * (2 - pairSpectralPoint p.2))

def pairTrivialTerm (n : ℕ) (p : ℝ × ℝ) : ℂ :=
  2 * Complex.exp ((Real.log p.1 : ℂ) * (-2*(n+1 : ℂ) - pairSpectralPoint p.2)) /
    ((2*(n+1 : ℂ) + pairSpectralPoint p.2 - 1) *
      (2*(n+1 : ℂ) + pairSpectralPoint p.2 + 1))

def pairTrivialCorrection (p : ℝ × ℝ) : ℂ := ∑' n, pairTrivialTerm n p

def pairShiftCorrection (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ)⁻¹ * (deriv riemannZeta (pairSpectralPoint p.2 - 1) /
    riemannZeta (pairSpectralPoint p.2 - 1))

end
end HigherCorrelations
