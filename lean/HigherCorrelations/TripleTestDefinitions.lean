import HigherCorrelations.ActualCorrelationDefinitions
import HigherCorrelations.TripleBudgetDefinitions

/-! UNCONDITIONAL definitions in the project inverse-Fourier convention.
The statistic sums all ordered actual occurrences; the anchor is slot zero. -/
namespace HigherCorrelations
noncomputable section

def tripleTestRegion : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1+p.2 < 1}
def tripleTestMargin (ε : ℝ) : Set (ℝ × ℝ) := {p | ε ≤ p.1 ∧ ε ≤ p.2 ∧ p.1+p.2 ≤ 1-ε}
def tripleTestBase (T : ℝ) : ℝ := T/(2*Real.pi)
def tripleTestL1 (φ : ℝ × ℝ → ℂ) : ℝ := ∫ p, ‖φ p‖

def tripleTestToMaster : MasterTriple ≃ MasterTriple where
  toFun v := ![v 1,v 2,v 0]
  invFun v := ![v 2,v 0,v 1]
  left_inv v := by funext i; fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl

def tripleTestArguments (T : ℝ) (v : MasterTriple) : ℂ × ℂ :=
  complexPair (actualGaps (meanSpacing T) v) (actualShifts (meanSpacing T) v)

def tripleTestStatistic (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ) : ℂ :=
  8*∑' v : MasterTriple, tripleMasterKernel ω T (tripleTestToMaster v)*complexFourier φ (tripleTestArguments T v)

def tripleTestFrequencyTerm (ω : ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (T : ℝ)
    (v : MasterTriple) (p : ℝ × ℝ) : ℂ :=
  φ p*(8*(tripleMasterCoefficient ((tripleTestBase T)^p.1) ((tripleTestBase T)^p.2)
    (tripleTestToMaster v)*tripleMasterKernel ω T (tripleTestToMaster v)))

end
end HigherCorrelations
