import HigherCorrelations.RationalTransferDefinitions

/-! UNCONDITIONAL reciprocal factors and the closed microscopic parameter box. -/
namespace HigherCorrelations
noncomputable section

def profileGapFactor (x h : ℝ) : ℂ := (4+((x:ℂ)-Complex.I*h)^2)⁻¹

def profileReciprocalSum (p q r : ℂ) : ℂ := p*q+p*r+q*r+12*p*q*r

def profileMicroscopicBox (R : ℝ) : Set (Fin 5 → ℝ) :=
  {p | |p 0|≤R ∧ |p 1|≤R ∧ |p 2|≤1/2 ∧ |p 3|≤1/2 ∧ |p 4|≤1/2}

end
end HigherCorrelations
