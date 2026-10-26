import HigherCorrelations.TripleMixedDiagonalDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL independent specifications. Intentional holes are confined to
verification challenges; no proof module is imported. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → a ≤ b →
    |tripleBudgetDiagonal a b-a/(2*b)*(1+Real.log (b/a))*Real.log (a*b)| ≤
      C*(a/b)*(1+Real.log (b/a)) := by sorry

theorem tripleMixedDiagonal_integer_split (A B N : ℕ) (hA : 1 ≤ A)
    (hAB : A ≤ B) (hBN : B ≤ N) :
    (∑ n ∈ Icc 0 N, tripleMixedDiagonalWeight A B n*(Λ n)^2) =
      (1/((A:ℝ)*B))*(∑ n ∈ Icc 0 A, (n:ℝ)*(Λ n)^2)+
      ((A:ℝ)/B)*(∑ n ∈ Ioc A B, (Λ n)^2/(n:ℝ))+
      ((A:ℝ)*B)*(∑ n ∈ Ioc B N, (Λ n)^2/(n:ℝ)^3) := by sorry

theorem tripleMixedDiagonal_finite_error_identity (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2)-
      (tripleMixedDiagonalModel a b-a*b*(2*Real.log Y+3)/(4*Y^2)) =
      a*b*(pairDiagonalCumulative Y-Y*Real.log Y)/Y^3-
      (1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u-u*Real.log u)+
      (a/b)*(∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2)+
      3*a*b*(∫ u in b..Y, (pairDiagonalCumulative u-u*Real.log u)/u^4) := by sorry

end
end HigherCorrelations
