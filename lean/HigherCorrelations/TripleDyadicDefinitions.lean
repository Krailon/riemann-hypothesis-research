import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! UNCONDITIONAL definition-only elementary dyadic majorants. -/
namespace HigherCorrelations
noncomputable section

def tripleNatBall (R c : ℝ) (n : ℕ) : ℝ := if 1≤n ∧ (n:ℝ)≤R then c else 0

def tripleMultiplicativeWeight (x : ℝ) (n : ℕ) : ℝ := min ((n:ℝ)/x) (x/n)

def tripleDyadicMoment (x : ℝ) (k : ℕ) (n : ℕ) : ℝ :=
  tripleMultiplicativeWeight x n^2*Real.log (2*n)^k

def tripleDyadicConstant (k : ℕ) : ℝ := 1+2*∑' j : ℕ, (1/2:ℝ)^j*(j+2:ℝ)^k

def tripleDyadicBall (x : ℝ) (k j : ℕ) (n : ℕ) : ℝ :=
  tripleNatBall ((2:ℝ)^(j+1)*x) ((1/4:ℝ)^j*((j+2:ℝ)*Real.log (2*x))^k) n

end
end HigherCorrelations
