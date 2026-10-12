import HigherCorrelations.PairZeroConvergence
import HigherCorrelations.PairPrimeConvergence

/-! PAIR-EF-CONVERGENCE with an existential absolute tail constant.
UNCONDITIONAL. The exact explicit-formula equality is a separate theorem. -/
namespace HigherCorrelations
noncomputable section
open Filter
open scoped Topology

theorem pairSeries_convergence :
    (∀ X t : ℝ, 1≤X → Summable (fun i => ‖pairZeroTerm i (X,t)‖) ∧
      Summable (fun n => ‖pairPrimeTerm n (X,t)‖)) ∧
    ContinuousOn pairZeroSeries pairSeriesDomain ∧
    ContinuousOn pairPrimeSeries pairSeriesDomain ∧
    (∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
      pairZeroTail X t U ≤ C*Real.sqrt X*Real.log U/U) :=
  ⟨fun X t hX => ⟨pairZeroTerm_summable X t hX, pairPrimeTerm_summable X t hX⟩,
    pairZeroSeries_continuous, pairPrimeSeries_continuous, pairZeroTail_bound⟩

theorem pairZero_cutoff_error : ∃ C : ℝ, 0<C ∧ ∀ X t U : ℝ, 1≤X → 2*(|t|+2)≤U →
    ‖pairZeroSeries (X,t) - ∑ i ∈ occurrenceCutoff U, pairZeroTerm i (X,t)‖ ≤
      C*Real.sqrt X*Real.log U/U := by
  obtain ⟨C,hC,hb⟩ := pairZeroTail_bound
  exact ⟨C,hC,fun X t U hX hU => (pairZero_cutoff_remainder X t U hX).trans (hb X t U hX hU)⟩

theorem pairPrimeTerm_at_knot (n : ℕ) (t : ℝ) :
    pairPrimeTerm n (n+1,t) = (ArithmeticFunction.vonMangoldt (n+1) : ℂ) *
      Complex.exp ((Real.log (n+1 : ℝ) : ℂ)*(-(1/2 : ℂ)-Complex.I*t)) := by
  simp [pairPrimeTerm, show (n+1 : ℝ) ≠ 0 by positivity]

theorem pairZeroTerm_at_one (i : ZeroOccurrence) (t : ℝ) :
    pairZeroTerm i (1,t) = 2 / (1+((t-occurrenceOrdinate i : ℝ)+Complex.I*occurrenceDisplacement i)^2) := by
  simp [pairZeroTerm]

end
end HigherCorrelations
