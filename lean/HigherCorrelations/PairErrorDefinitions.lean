import HigherCorrelations.PairExactDefinitions

/-! Definition-only interface for the named uniform remainders in PAIR-EF-001.
UNCONDITIONAL. The principal logarithm and positive-real exponential powers
agree with the exact pair formula. Constants do not depend on X or t. -/
namespace HigherCorrelations
noncomputable section

def pairChi (z : ℂ) : ℂ :=
  Complex.exp (z * (Real.log 2 : ℂ)) *
    Complex.exp ((z-1) * (Real.log Real.pi : ℂ)) *
    Complex.sin ((Real.pi : ℂ) * z / 2) * Complex.Gamma (1-z)

def pairArchError (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ)⁻¹ * (-deriv pairChi (pairSpectralPoint p.2-1) /
    pairChi (pairSpectralPoint p.2-1) - (Real.log (|p.2|+2) : ℂ))

def pairDSError (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ)⁻¹ * (deriv riemannZeta (2-pairSpectralPoint p.2) /
    riemannZeta (2-pairSpectralPoint p.2))

def pairDSConstant : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt (n+1) / (n+1 : ℝ)^(3/2 : ℝ)

def pairArchConstant : ℝ := Real.log (2*Real.pi) + Real.pi + Real.log 2 + 4/3

end
end HigherCorrelations
