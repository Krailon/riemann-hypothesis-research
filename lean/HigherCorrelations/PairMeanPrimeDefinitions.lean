import HigherCorrelations.PairMeanDefinitions
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Definition-only prime specialization of PAIR-MEANVALUE-001.
Index n denotes the positive integer n+1, including the zero coefficient at one.
Nearby pairs are ordered, distinct indices with a strict logarithmic cutoff. -/
namespace HigherCorrelations
noncomputable section

def pairMeanPrimeFrequency (n : ℕ) : ℝ := -Real.log (n+1:ℝ)/(2*Real.pi)
def pairMeanPrimeCoefficient (X : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt (n+1)*Real.exp (Real.log (n+1:ℝ)*(-(1/2:ℝ)))*
    min ((n+1:ℝ)/X) (X/(n+1:ℝ))
def pairMeanPrimeDiagonal (X : ℝ) : ℝ := ∑' n, pairMeanPrimeCoefficient X n^2
def pairMeanPrimeNearby (X δ : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, if p.1 ≠ p.2 ∧ |Real.log ((p.1+1:ℝ)/(p.2+1:ℝ))| < 2*Real.pi*δ
    then pairMeanPrimeCoefficient X p.1*pairMeanPrimeCoefficient X p.2 else 0

end
end HigherCorrelations
