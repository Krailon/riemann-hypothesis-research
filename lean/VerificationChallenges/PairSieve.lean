import HigherCorrelations.PairSieveDefinitions
import OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound

/-! UNCONDITIONAL statement specifications. Deliberately unfinished challenge
proofs are isolated from the solution import graph. -/
namespace HigherCorrelations
noncomputable section
open Finset OAI.Problem337
open scoped ArithmeticFunction.vonMangoldt

theorem pairSieve_prime_bound (U h : ℕ) (hU : 2 ≤ U) (hh : 2 ∣ h) (hh0 : h ≠ 0) :
    ((pairSievePrimes U h).card : ℝ)*Real.log U^2 ≤ pairSievePrimeConstant*pairSieveBadFactor h*U := by sorry

theorem pairSieve_denominator_lower (h N : ℕ) (hh : 2 ∣ h) (hh0 : h ≠ 0) (hN : 1 ≤ N) :
    Real.log N^2 ≤ pairSieveBadFactor h*GoldbachSelberg.denominator h (primorial (N^2)) (N^2) := by sorry

theorem pairSieveBadFactor_sum_le (N : ℕ) :
    (∑ h ∈ Icc 1 N, pairSieveBadFactor h) ≤ Real.exp 3*N := by sorry

theorem pairSieveProperPowers_weighted (U : ℕ) (hU : 1 ≤ U) :
    ((pairSieveProperPowers U).card : ℝ)*Real.log U^2 ≤ pairSievePowerConstant*U := by sorry

theorem pairSieveNearbyNat_sum (U V : ℕ) :
    (∑ p ∈ pairSieveNearbyNat U V, Λ p.1*Λ p.2) =
      2*∑ h ∈ Icc 1 V, pairSieveShiftMangoldt U h := by sorry

theorem pairSieveNearby_bound (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (∑ p ∈ pairSieveNearby U V, Λ p.1*Λ p.2) ≤ pairSieveCountConstant*U*V := by sorry

theorem pairSieveNearby_empty (U V : ℝ) (hV : V < 1) : pairSieveNearby U V = ∅ := by sorry

theorem pairSieve_log_comparable (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : δ ≤ 1/2) (hband : |Real.log (a/b)| < 2*Real.pi*δ) :
    a ≤ Real.exp Real.pi*b ∧ b ≤ Real.exp Real.pi*a := by sorry

theorem pairSieve_coefficients_head (X : ℝ) (hX : 1 ≤ X) (m n : ℕ)
    (hm : (m+1:ℝ) ≤ X) (hn : (n+1:ℝ) ≤ X) :
    pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n ≤ Λ (m+1)*Λ (n+1)/X := by sorry

theorem pairSieve_coefficients_tail (X r : ℝ) (hX : 1 ≤ X) (hr : 0 < r) (m n : ℕ)
    (hm : r ≤ (m+1:ℝ)) (hn : r ≤ (n+1:ℝ)) :
    pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n ≤
      (X^2/r^3)*(Λ (m+1)*Λ (n+1)) := by sorry

theorem pairSieveBall_double_summable (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) :
    Summable (fun q : ℕ × (ℕ × ℕ) => pairSieveBall X δ ((2:ℝ)^q.1*X) q.2) := by sorry

theorem pairMeanPrimeNearby_bound (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2) :
    pairMeanPrimeNearby X δ ≤ pairSieveNearbyConstant*δ*X := by sorry

theorem pairMeanPrimeNearby_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ X δ : ℝ, 1 ≤ X → 0 < δ → δ ≤ 1/2 → pairMeanPrimeNearby X δ ≤ C*δ*X := by sorry

theorem pairMeanPrimeNearby_zero (X : ℝ) : pairMeanPrimeNearby X 0 = 0 := by sorry

theorem pairMeanPrimeNearby_endpoint (X : ℝ) (hX : 1 ≤ X) :
    pairMeanPrimeNearby X (1/2) ≤ pairSieveNearbyConstant*X/2 := by sorry

theorem pairMeanPrimeNearby_unit (δ : ℝ) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/2) :
    pairMeanPrimeNearby 1 δ ≤ pairSieveNearbyConstant*δ := by sorry

theorem pairMeanPrimeNearby_boundary_term (X δ : ℝ) (m n : ℕ)
    (he : |Real.log ((m+1:ℝ)/(n+1:ℝ))| = 2*Real.pi*δ) :
    (if m ≠ n ∧ |Real.log ((m+1:ℝ)/(n+1:ℝ))| < 2*Real.pi*δ then
      pairMeanPrimeCoefficient X m*pairMeanPrimeCoefficient X n else 0) = 0 := by sorry
end
end HigherCorrelations
