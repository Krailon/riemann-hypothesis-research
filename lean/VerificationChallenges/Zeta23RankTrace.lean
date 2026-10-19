import HigherCorrelations.Zeta23Definitions

namespace HigherCorrelations
noncomputable section
open scoped ComplexOrder

theorem zeta23_rank_trace {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : matrixPositiveIndex hQ ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * P.trace.re - c ^ 2 / 4 * r + 2 * c * Q.trace.re - c ^ 2 * b
      ≤ matrixFrobeniusSq (P + Q) := by sorry

theorem zeta23_rank_trace_two {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : matrixPositiveIndex hQ ≤ b) :
    2 * P.trace.re + 4 * Q.trace.re - 4 * (b : ℝ) - matrixFrobeniusSq (P + Q)
      ≤ (r : ℝ) := by sorry

theorem zeta23_rank_trace_empty (P Q : Matrix (Fin 0) (Fin 0) ℂ) (c : ℝ) :
    c * P.trace.re + 2 * c * Q.trace.re = matrixFrobeniusSq (P + Q) := by sorry

end
end HigherCorrelations
