import HigherCorrelations.Zeta23Definitions
import Zeta23.LinAlg.RankTrace

/-! UNCONDITIONAL finite matrix inequalities imported from the pinned Zeta23 source.
These statements impose no positivity assumption on Weil's full form. -/
namespace HigherCorrelations
noncomputable section
open scoped ComplexOrder

theorem zeta23_rank_trace {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : matrixPositiveIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * P.trace.re - c ^ 2 / 4 * r + 2 * c * Q.trace.re - c ^ 2 * b
      ≤ matrixFrobeniusSq (P + Q) := by
  exact RHLinalg.rank_trace_ineq hP hQ hr hb hc

theorem zeta23_rank_trace_two {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : matrixPositiveIndex hQ ≤ b) :
    2 * P.trace.re + 4 * Q.trace.re - 4 * (b : ℝ) - matrixFrobeniusSq (P + Q)
      ≤ (r : ℝ) := by
  exact RHLinalg.rank_trace_ineq_two hP hQ hr hb

theorem zeta23_rank_trace_empty (P Q : Matrix (Fin 0) (Fin 0) ℂ) (c : ℝ) :
    c * P.trace.re + 2 * c * Q.trace.re = matrixFrobeniusSq (P + Q) := by
  simp [Matrix.trace, matrixFrobeniusSq]

end
end HigherCorrelations
