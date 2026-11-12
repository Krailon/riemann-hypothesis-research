import HigherCorrelations.PairErrorDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! UNCONDITIONAL conventions for the asymmetric approximate functional equation.
The remainder is the actual difference, not an assumed error witness. Every cutoff
is inclusive; positive integers alone occur in the two polynomials. No asymptotic
bound is asserted by these definitions. -/
namespace HigherCorrelations
noncomputable section

def afePoint (σ t : ℝ) : ℂ := σ + t * Complex.I

def afePolynomial (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s)

def afeHeight (t : ℝ) : ℝ := |t| / (2 * Real.pi)

def afePhase (σ t : ℝ) : ℂ :=
  (afeHeight t ^ (1/2-σ) : ℝ) *
    Complex.exp (((-t * Real.log (afeHeight t / Real.exp 1) +
      SignType.sign t * Real.pi / 4 : ℝ) : ℂ) * Complex.I)

def afeRemainder (s : ℂ) (x y : ℝ) : ℂ :=
  riemannZeta s - afePolynomial s x - pairChi s * afePolynomial (1-s) y

def afePhaseRemainder (σ t x y : ℝ) : ℂ :=
  riemannZeta (afePoint σ t) - afePolynomial (afePoint σ t) x -
    afePhase σ t * afePolynomial (1-afePoint σ t) y

/-- The shorter polynomial used in the twisted second moment. -/
def afeTwistShort (μ₁ μ₂ t : ℝ) : ℝ :=
  Real.sqrt (t * μ₁ / (2 * Real.pi * μ₂))

/-- The longer polynomial used in the twisted second moment. -/
def afeTwistLong (μ₁ μ₂ t : ℝ) : ℝ :=
  Real.sqrt (t * μ₂ / (2 * Real.pi * μ₁))

/-- One-step error of the logarithmic Stirling main term. -/
def afeStirlingStep (z : ℂ) : ℂ :=
  (z+1/2)*Complex.log (1+z⁻¹)-1

def afeStirlingMain (z : ℂ) : ℂ := (z-1/2)*Complex.log z-z

def afeStirlingCorrection (z : ℂ) : ℂ := ∑' n : ℕ, afeStirlingStep (z+n)

def afeGammaVerticalError (a t : ℝ) : ℂ :=
  ((a:ℂ)-t*Complex.I-1/2)*Complex.log (1+(a/t:ℝ)*Complex.I) - a +
    afeStirlingCorrection ((a:ℂ)-t*Complex.I)

/-- Logarithm with its cut on the positive real axis; its imaginary part is in
`(0,2*pi)` off the cut. Boundary values must be taken as one-sided limits. -/
def afeHankelLog (z : ℂ) : ℂ := Complex.log (-z) + Real.pi * Complex.I

def afeHankelPower (s z : ℂ) : ℂ := Complex.exp ((s-1)*afeHankelLog z)

def afeHankelKernel (s : ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  afeHankelPower s z * Complex.exp (-(m:ℂ)*z) / (Complex.exp z-1)

def afeHankelPrefactor (s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*s*Complex.I) * Complex.Gamma (1-s) /
    (2*Real.pi*Complex.I)

/-- Pullback of the Hankel differential under z=exp(w). -/
def afeHankelLift (s : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (s*w) * Complex.exp (-(m:ℂ)*Complex.exp w) /
    (Complex.exp (Complex.exp w)-1)

def afeHankelRayWeight (m : ℕ) (r : ℝ) (u : ℝ) : ℂ :=
  (Set.Ioi r).indicator (fun u : ℝ =>
    Complex.exp (-((m:ℝ)*u:ℝ))/(Complex.exp (u:ℂ)-1)) u

end
end HigherCorrelations
