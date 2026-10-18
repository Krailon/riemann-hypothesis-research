import HigherCorrelations.PairErrorDefinitions
import HigherCorrelations.PairPrimeMeanDefinitions

/-! UNCONDITIONAL definition-only interface for the full explicit-formula mean square.
All integrals are on [0,T]; the actual four remainders are retained separately. -/
namespace HigherCorrelations
noncomputable section

inductive PairRemainderKind where
  | arch | ds | pole | trivial
  deriving DecidableEq

instance : Fintype PairRemainderKind :=
  ⟨{.arch, .ds, .pole, .trivial}, by intro j; cases j <;> simp⟩

def pairRHSArch (X t : ℝ) : ℂ := (Real.log (t+2)/X : ℝ)
def pairRHSRemainder (j : PairRemainderKind) (X t : ℝ) : ℂ := match j with
  | .arch => pairArchError (X,t)
  | .ds => pairDSError (X,t)
  | .pole => pairPoleCorrection (X,t)
  | .trivial => pairTrivialCorrection (X,t)
def pairRHSRemainderSum (X t : ℝ) : ℂ := ∑ j, pairRHSRemainder j X t
def pairRHS (X t : ℝ) : ℂ := -pairPrimeSeries (X,t)+pairRHSArch X t+pairRHSRemainderSum X t
def pairRHSSquare (X T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, ‖pairRHS X t‖^2
def pairZeroMeanSquare (X T : ℝ) : ℝ := ∫ t in (0:ℝ)..T, ‖pairZeroSeries (X,t)‖^2
def pairRHSL2 (f : ℝ → ℂ) (T : ℝ) : ℝ := Real.sqrt (∫ t in (0:ℝ)..T, ‖f t‖^2)
def pairRHSArchSquareError (X T : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..T, ‖pairRHSArch X t‖^2)-T*Real.log T^2/X^2
def pairRHSPrimeArchError (X T : ℝ) : ℝ :=
  -2*(∫ t in (0:ℝ)..T, pairPrimeSeries (X,t)*star (pairRHSArch X t)).re
def pairRHSPrimeError (j : PairRemainderKind) (X T : ℝ) : ℝ :=
  -2*(∫ t in (0:ℝ)..T, pairPrimeSeries (X,t)*star (pairRHSRemainder j X t)).re
def pairRHSArchError (j : PairRemainderKind) (X T : ℝ) : ℝ :=
  2*(∫ t in (0:ℝ)..T, pairRHSArch X t*star (pairRHSRemainder j X t)).re
def pairRHSRemainderSquare (X T : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, ‖pairRHSRemainderSum X t‖^2
def pairRHSSmallError (X T : ℝ) : ℝ := pairRHSArchSquareError X T+
  pairRHSArchError .arch X T+pairRHSArchError .ds X T
def pairRHSLargeError (X T : ℝ) : ℝ := pairPrimeMeanDiagonalError X T+
  pairPrimeMeanOffdiag X T+pairRHSPrimeArchError X T+
  (∑ j, pairRHSPrimeError j X T)+pairRHSArchError .pole X T+
  pairRHSArchError .trivial X T+pairRHSRemainderSquare X T

end
end HigherCorrelations
