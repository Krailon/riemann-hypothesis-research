import HigherCorrelations.TripleQuadrantDefinitions

/-! UNCONDITIONAL boundary domains, logarithmic constant and explicit residual majorant. -/
namespace HigherCorrelations
noncomputable section
open Set

def tripleBoundaryBox : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1

def tripleBoundaryLogConstant : ℝ := 1+Real.log (2*Real.pi)+Real.log 3

def tripleBoundaryMajorant (A H D W V T κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  let b := Real.log (tripleTestBase T)
  let L := Real.log (2*T+2)
  A*V*(L^2*(Real.exp (-((2*b)*p.1))*Real.exp (-((2*b)*p.2)))+
    (L^3/T+(tripleTestBase T)^(-κ)*L^4)) +
  H*(1+W)*(L*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2)))+
    L^2*(Real.exp (-(b*p.1))*Real.exp (-(b*p.2)))) +
  (D*L+4*b/T)*(Real.exp (-(b*p.1))+Real.exp (-(b*p.2))) +
  3456*tripleResonanceDecayConstant*
    (Real.exp (-((b/4)*p.1))*Real.exp (-((b/4)*p.2)))

end
end HigherCorrelations
