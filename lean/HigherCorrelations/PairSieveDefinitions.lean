import HigherCorrelations.PairMeanPrimeDefinitions
import OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal

/-! UNCONDITIONAL. Definition-only interfaces for the nearby-prime sieve
milestone and its independently specified Comparator challenges. -/
namespace HigherCorrelations
noncomputable section
open Finset OAI.Problem337
open scoped ArithmeticFunction.vonMangoldt

/-- Product weight on a finite subset. -/
def pairSieveWeight {α : Type*} (w : α → ℝ) (s : Finset α) : ℝ := ∏ p ∈ s, w p

/-- Truncated product measure on squarefree products. -/
def pairSieveSubsetSum (s : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ s.powerset, if (∏ p ∈ a, p) ≤ N then pairSieveWeight w a else 0

/-- Reciprocal totient weight at a prime. -/
def pairSieveReciprocal (p : ℕ) : ℝ := 1 / ((p : ℝ)-1)

/-- Positive first coordinates; no quotient by interchange of coordinates. -/
def pairSievePrimes (U h : ℕ) : Finset ℕ :=
  (Icc 1 U).filter (fun n => n.Prime ∧ (n+h).Prime)

def pairSieveSifted (U h P : ℕ) : Finset ℕ :=
  (Icc 1 U).filter (fun n => P.Coprime (n*(n+h)))

/-- Averagable divisor factor, including the prime two. -/
def pairSieveBadFactor (h : ℕ) : ℝ :=
  ∏ p ∈ h.primeFactors, (1+pairSieveReciprocal p)^2

/-- Local factor of the actual Selberg normalizer. -/
def pairSieveLocalWeight (h p : ℕ) : ℝ :=
  goldbachSieveDensity h p * (1-goldbachSieveDensity h p)⁻¹

def pairSieveExcess (p : ℕ) : ℝ :=
  2*pairSieveReciprocal p+pairSieveReciprocal p^2

def pairSievePrimeConstant : ℝ := 256*(1+81*16^6+512)

def pairSieveProperPowers (U : ℕ) : Finset ℕ :=
  (Icc 1 U).filter (fun n => IsPrimePow n ∧ ¬n.Prime)

def pairSievePowerConstant : ℝ := 128+1024/Real.log 2

def pairSieveShiftMangoldt (U h : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 U, if n+h ≤ U then Λ n*Λ (n+h) else 0

def pairSieveActive (U h : ℕ) : Finset ℕ :=
  (Icc 1 U).filter (fun n => n+h ≤ U ∧ IsPrimePow n ∧ IsPrimePow (n+h))

def pairSieveCountConstant : ℝ :=
  2*(pairSievePrimeConstant*Real.exp 3+4+2*pairSievePowerConstant)

def pairSievePositivePairs (U V : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 U) ×ˢ (Icc 1 U)).filter (fun p => p.1 < p.2 ∧ p.2-p.1 ≤ V)

def pairSieveNearbyNat (U V : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 U) ×ˢ (Icc 1 U)).filter (fun p => p.1 ≠ p.2 ∧ Nat.dist p.1 p.2 ≤ V)

def pairSieveNearby (U V : ℝ) : Finset (ℕ × ℕ) :=
  ((Icc 1 ⌊U⌋₊) ×ˢ (Icc 1 ⌊U⌋₊)).filter
    (fun p => p.1 ≠ p.2 ∧ |(p.1 : ℝ)-p.2| ≤ V)

def pairSieveNearbyConstant : ℝ :=
  32*Real.pi*(Real.exp Real.pi)^3*pairSieveCountConstant

def pairSieveBall (X δ R : ℝ) (p : ℕ × ℕ) : ℝ :=
  if (p.1+1,p.2+1) ∈ pairSieveNearby R (2*Real.pi*δ*R) then
    (8*(Real.exp Real.pi)^3*X^2/R^3)*(Λ (p.1+1)*Λ (p.2+1)) else 0

end
end HigherCorrelations
