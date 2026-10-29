import HigherCorrelations.TripleQuadrantDefinitions

/-! UNCONDITIONAL quadrant supremum and first-derivative seminorm conventions. -/
namespace HigherCorrelations
noncomputable section

def tripleQuadrantSup (f : ℝ × ℝ → ℂ) : ℝ := sSup ((fun p => ‖f p‖) '' tripleQuadrant)

def tripleQuadrantN1 (ψ : ℝ × ℝ → ℂ) : ℝ :=
  tripleQuadrantSup ψ + tripleQuadrantSup (fun p => fderiv ℝ ψ p (1,0)) +
    tripleQuadrantSup (fun p => fderiv ℝ ψ p (0,1))

end
end HigherCorrelations
