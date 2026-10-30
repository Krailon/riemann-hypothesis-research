import HigherCorrelations.PairSeriesDefinitions

/-! UNCONDITIONAL positive-base domains for the existing full-zero series. -/
namespace HigherCorrelations
noncomputable section

def signedSeriesDomain : Set (ℝ × ℝ) := {p | 0 < p.1}
def signedSeriesRectangle (a b H : ℝ) : Set (ℝ × ℝ) :=
  {p | a ≤ p.1 ∧ p.1 ≤ b ∧ |p.2| ≤ H}

end
end HigherCorrelations
