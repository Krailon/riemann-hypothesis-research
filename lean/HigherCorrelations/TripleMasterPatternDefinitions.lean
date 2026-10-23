import HigherCorrelations.TripleMasterDefinitions

/-! UNCONDITIONAL definition-only interfaces for occurrence-index subseries.
Equality here is equality of the full multiplicity-bearing occurrence index,
not equality of complex values or ordinates. -/
namespace HigherCorrelations
noncomputable section

abbrev MasterPatternTriple (p : TriplePattern) :=
  {v : MasterTriple // classifyTriple v = p}

abbrev MasterUnequalPair := {q : ZeroOccurrence × ZeroOccurrence // q.1 ≠ q.2}

abbrev MasterDistinctTriple :=
  {v : MasterTriple // v 0 ≠ v 1 ∧ v 0 ≠ v 2 ∧ v 1 ≠ v 2}

/-- B includes the factor eight; every pattern contribution uses this convention. -/
def tripleMasterKernelTerm (ω : ℝ → ℝ) (T X Y : ℝ) (v : MasterTriple) : ℂ :=
  8 * (tripleMasterCoefficient X Y v * tripleMasterKernel ω T v)

def tripleMasterPatternSeries (ω : ℝ → ℝ) (T X Y : ℝ) (p : TriplePattern) : ℂ :=
  ∑' v : MasterPatternTriple p, tripleMasterKernelTerm ω T X Y v.val

end
end HigherCorrelations
