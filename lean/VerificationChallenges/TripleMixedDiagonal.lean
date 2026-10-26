import HigherCorrelations.TripleMixedDiagonalDefinitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! UNCONDITIONAL independent specifications. Intentional holes are confined to
verification challenges; no proof module is imported. -/
namespace HigherCorrelations
noncomputable section
open Finset MeasureTheory Filter
open scoped Topology ArithmeticFunction.vonMangoldt

theorem tripleMixedDiagonal_middle_derivative (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => (1:ℝ)/t) (-1/u^2) u := by sorry

theorem tripleMixedDiagonal_middle_abel (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Λ n)^2/(n:ℝ)) =
      pairDiagonalCumulative b/b-pairDiagonalCumulative a/a+
        (∫ u in a..b, pairDiagonalCumulative u/u^2) := by sorry

theorem tripleMixedDiagonal_finite_abel (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2) =
      a*b*pairDiagonalCumulative Y/Y^3-
      (1/(a*b))*(∫ u in (1:ℝ)..a, pairDiagonalCumulative u)+
      (a/b)*(∫ u in a..b, pairDiagonalCumulative u/u^2)+
      3*a*b*(∫ u in b..Y, pairDiagonalCumulative u/u^4) := by sorry

theorem tripleMixedDiagonal_middle_integral (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, Real.log u/u) = (Real.log b^2-Real.log a^2)/2 := by sorry

theorem tripleMixedDiagonal_cumulative_div_integrable (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (k : ℕ) :
    IntervalIntegrable (fun u : ℝ => pairDiagonalCumulative u/u^k) volume a b := by sorry

theorem tripleMixedDiagonal_error_integral_split (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (k : ℕ) :
    (∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^k) =
      (∫ u in a..b, pairDiagonalCumulative u/u^k)-
      (∫ u in a..b, u*Real.log u/u^k) := by sorry

theorem tripleMixedDiagonalWeight_knots (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a/(a*b) = a/(b*a) ∧ a/(b*b) = a*b/b^3 := by sorry

theorem tripleMixedDiagonal_coefficient (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) (n : ℕ) :
    pairMeanPrimeCoefficient a n*pairMeanPrimeCoefficient b n =
      tripleMixedDiagonalWeight a b (n+1)*(Λ (n+1))^2 := by sorry

theorem tripleMixedDiagonalWeight_summable (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun n : ℕ => tripleMixedDiagonalWeight a b n*(Λ n)^2) := by sorry

theorem tripleMixedDiagonal_weight (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    tripleBudgetDiagonal a b = ∑' n : ℕ, tripleMixedDiagonalWeight a b n*(Λ n)^2 := by sorry

theorem tripleMixedDiagonal_partial_tendsto (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 0 N, tripleMixedDiagonalWeight a b n*(Λ n)^2)
      atTop (nhds (tripleBudgetDiagonal a b)) := by sorry

theorem tripleMixedDiagonal_finite_split (a b Y : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2) =
      (1/(a*b))*(∑ n ∈ Icc 0 ⌊a⌋₊, (n:ℝ)*(Λ n)^2)+
      (a/b)*(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Λ n)^2/(n:ℝ))+
      (a*b)*(∑ n ∈ Ioc ⌊b⌋₊ ⌊Y⌋₊, (Λ n)^2/(n:ℝ)^3) := by sorry

theorem tripleMixedDiagonal_boundary_tendsto (a b : ℝ) :
    Tendsto (fun Y : ℝ => a*b*(2*Real.log Y+3)/(4*Y^2)) atTop (nhds 0) := by sorry

theorem tripleMixedDiagonal_model_bound_of_cumulative (K a b : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |tripleBudgetDiagonal a b-tripleMixedDiagonalModel a b| ≤ K*(a/b)*(3+Real.log (b/a)) := by sorry

theorem tripleMixedDiagonal_model_correction (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |tripleMixedDiagonalModel a b-tripleMixedDiagonalMain a b| ≤ (a/b)*(1+Real.log (b/a)) := by sorry

theorem tripleMixedDiagonal_asymptotic_of_cumulative (K : ℝ) (hK : 0 < K)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u)
    (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |tripleBudgetDiagonal a b-tripleMixedDiagonalMain a b| ≤
      (3*K+1)*(a/b)*(1+Real.log (b/a)) := by sorry

theorem tripleMixedDiagonal_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → a ≤ b →
    |tripleBudgetDiagonal a b-a/(2*b)*(1+Real.log (b/a))*Real.log (a*b)| ≤
      C*(a/b)*(1+Real.log (b/a)) := by sorry

theorem tripleMixedDiagonal_asymptotic_symmetric : ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ,
    1 ≤ a → 1 ≤ b →
    |tripleBudgetDiagonal a b-tripleMixedDiagonalMain (min a b) (max a b)| ≤
      C*(min a b/max a b)*(1+Real.log (max a b/min a b)) := by sorry

theorem tripleMixedDiagonalWeight_self (a u : ℝ) :
    tripleMixedDiagonalWeight a a u = pairDiagonalWeight a u := by sorry

theorem tripleMixedDiagonalMain_self (a : ℝ) (ha : 1 ≤ a) :
    tripleMixedDiagonalMain a a = Real.log a := by sorry

theorem tripleMixedDiagonalModel_self (a : ℝ) (ha : 1 ≤ a) :
    tripleMixedDiagonalModel a a = Real.log a+1-1/(4*a^2) := by sorry

theorem tripleMixedDiagonal_unit_model (b : ℝ) :
    tripleMixedDiagonalModel 1 b =
      (1/(2*b))*(1+Real.log b)*Real.log b+(1/b)*(1+Real.log b)-1/(4*b) := by sorry

theorem tripleMixedDiagonal_unit_unit :
    tripleMixedDiagonalMain 1 1 = 0 ∧ tripleMixedDiagonalModel 1 1 = 3/4 := by sorry

theorem tripleMixedDiagonal_self_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 1 ≤ a →
    |pairMeanPrimeDiagonal a-Real.log a| ≤ C := by sorry

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

theorem tripleMixedDiagonal_middle_error (K a b : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |∫ u in a..b, (pairDiagonalCumulative u-u*Real.log u)/u^2| ≤ K*Real.log (b/a) := by sorry

theorem tripleMixedDiagonal_finite_error_bound (K a b Y : ℝ) (hK : 0 < K)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbY : b ≤ Y)
    (hE : ∀ u : ℝ, 1 ≤ u → |pairDiagonalCumulative u-u*Real.log u| ≤ K*u) :
    |(∑ n ∈ Icc 0 ⌊Y⌋₊, tripleMixedDiagonalWeight a b n*(Λ n)^2)-
      (tripleMixedDiagonalModel a b-a*b*(2*Real.log Y+3)/(4*Y^2))| ≤
      K*(a/b)*(3+Real.log (b/a)) := by sorry

end
end HigherCorrelations
