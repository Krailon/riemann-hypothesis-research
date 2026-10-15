import HigherCorrelations.PairErrorDefinitions
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! Definition-only specifications for PAIR-EF-001. Intentional unfinished
challenge proofs, never imported by solution modules. UNCONDITIONAL. -/
namespace HigherCorrelations
noncomputable section
open Complex

theorem pairArchError_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairArchError (X,t)‖ ≤ pairArchConstant / X := by sorry

theorem pairChi_functional_eq (z : ℂ) (hz : z.re < 0) :
    riemannZeta z = pairChi z * riemannZeta (1-z) := by sorry

theorem pairChi_logDeriv (t : ℝ) :
    deriv pairChi (pairSpectralPoint t-1) / pairChi (pairSpectralPoint t-1) =
      (Real.log (2*Real.pi):ℂ) + (Real.pi:ℂ)/2 *
        cot ((Real.pi:ℂ)*(pairSpectralPoint t-1)/2) - digamma (2-pairSpectralPoint t) := by sorry

theorem pairShift_logDeriv_split (t : ℝ) :
    -deriv riemannZeta (pairSpectralPoint t-1) / riemannZeta (pairSpectralPoint t-1) =
      -deriv pairChi (pairSpectralPoint t-1) / pairChi (pairSpectralPoint t-1) +
        deriv riemannZeta (2-pairSpectralPoint t) / riemannZeta (2-pairSpectralPoint t) := by sorry

theorem pairDSConstant_approximation (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ pairDSConstant - ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℝ)^(3/2:ℝ) ∧
    pairDSConstant - ∑ n ∈ Finset.range N,
      ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℝ)^(3/2:ℝ) ≤ 16*(N:ℝ)^(-1/4:ℝ) := by sorry

theorem pairDigamma_remainder_bound (z : ℂ) (hz : 0 < z.re) :
    ‖digamma z-log z‖ ≤ 2/‖z‖ := by sorry

theorem pairDSConstant_summable : Summable (fun n : ℕ =>
    ArithmeticFunction.vonMangoldt (n+1) / (n+1 : ℝ)^(3/2 : ℝ)) := by sorry

theorem pairDSError_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairDSError (X,t)‖ ≤ pairDSConstant / X := by sorry

theorem pairPoleCorrection_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairPoleCorrection (X,t)‖ ≤ 4 * X^(1/2 : ℝ) / (1+t^2) := by sorry

theorem pairTrivialCorrection_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairTrivialCorrection (X,t)‖ ≤ 12 * X^(-5/2 : ℝ) / (|t|+2) := by sorry

theorem pairUniform_formula (X t : ℝ) (hX : 1 ≤ X) :
    pairZeroSeries (X,t) = -pairPrimeSeries (X,t) +
      (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ) + pairArchError (X,t)+pairDSError (X,t) +
      pairPoleCorrection (X,t)+pairTrivialCorrection (X,t) := by sorry

theorem pairUniform_named_bounds (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairArchError (X,t)‖ ≤ pairArchConstant/X ∧
    ‖pairDSError (X,t)‖ ≤ pairDSConstant/X ∧
    ‖pairPoleCorrection (X,t)‖ ≤ 4*X^(1/2:ℝ)/(1+t^2) ∧
    ‖pairTrivialCorrection (X,t)‖ ≤ 12*X^(-5/2:ℝ)/(|t|+2) := by sorry

theorem pairUniform_remainder_bound (X t : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroSeries (X,t)+pairPrimeSeries (X,t)-
      (X:ℂ)⁻¹*(Real.log (|t|+2):ℂ)‖ ≤
      (pairArchConstant+pairDSConstant)/X +
        4*X^(1/2:ℝ)/(1+t^2)+12*X^(-5/2:ℝ)/(|t|+2) := by sorry

theorem pairUniform_endpoint (t : ℝ) :
    pairZeroSeries (1,t) = -pairPrimeSeries (1,t)+(Real.log (|t|+2):ℂ)+
      pairArchError (1,t)+pairDSError (1,t)+pairPoleCorrection (1,t)+
        pairTrivialCorrection (1,t) := by sorry

theorem pairUniform_zero_height (X : ℝ) (hX : 1 ≤ X) :
    ‖pairZeroSeries (X,0)+pairPrimeSeries (X,0)-(X:ℂ)⁻¹*(Real.log 2:ℂ)‖ ≤
      (pairArchConstant+pairDSConstant)/X+4*X^(1/2:ℝ)+6*X^(-5/2:ℝ) := by sorry

end
end HigherCorrelations
