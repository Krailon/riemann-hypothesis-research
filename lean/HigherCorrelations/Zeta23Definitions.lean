import HigherCorrelations.LocalZeroCountDefinitions
import Mathlib.Analysis.Matrix.PosDef

/-! Definition-only interface for selected Zeta23 imports. UNCONDITIONAL.
Ordinate windows use (a,b]; occurrenceInterval continues to use [a,b]. -/
namespace HigherCorrelations
noncomputable section

def occurrenceWindow (a b : ℝ) : Finset ZeroOccurrence := by
  classical
  exact (occurrenceInterval a b).filter (fun i => a < occurrenceOrdinate i)

def zetaDyadicMain (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * (Real.log (T / (2 * Real.pi)) + 2 * Real.log 2 - 1)

def matrixPositiveIndex {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => 0 < hQ.eigenvalues i)).card

def matrixFrobeniusSq {n : Type*} [Fintype n] (A : Matrix n n ℂ) : ℝ :=
  (A.conjTranspose * A).trace.re

end
end HigherCorrelations
