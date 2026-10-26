import HigherCorrelations.TripleDyadicDefinitions
import HigherCorrelations.TripleLogGapDefinitions
import HigherCorrelations.TriplePrimeResonanceDefinitions

/-! UNCONDITIONAL coefficient and ordered divisor-convolution interface. -/
namespace HigherCorrelations
noncomputable section

def tripleArithmeticCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * tripleMultiplicativeWeight x n

def tripleArithmeticConvolution (X Y : ℝ) (r : ℕ) : ℝ :=
  ∑ d ∈ r.divisors, tripleArithmeticCoefficient X d * tripleArithmeticCoefficient Y (r/d)

def tripleLogCoefficient (x : ℝ) (n : LogGapIndex) : ℂ := tripleArithmeticCoefficient x n.val

def tripleLogConvolution (X Y : ℝ) (n : LogGapIndex) : ℂ := tripleArithmeticConvolution X Y n.val

def triplePrimeMassRatio : ℝ := 1/Real.sqrt 2

def triplePrimeMassConstant : ℝ := 1+2*∑' j : ℕ, triplePrimeMassRatio^j*(j+1:ℝ)

def triplePrimeMassBall (x : ℝ) (j n : ℕ) : ℝ :=
  tripleNatBall ((2:ℝ)^(j+1)*x)
    ((1/(2*Real.sqrt 2):ℝ)^j*(j+1:ℝ)*Real.log (2*x)/Real.sqrt x) n

end
end HigherCorrelations
