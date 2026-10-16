import HigherCorrelations.PairSieveSubset
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBounds

/-! UNCONDITIONAL. The one-dimensional harmonic lower bound, translated to
finite subset sums. The sieve used here is a bookkeeping object with zero mass. -/
namespace HigherCorrelations
noncomputable section
open Finset
open scoped ArithmeticFunction.zeta

/-- Divisor sums over a squarefree integer are subset sums over its primes. -/
theorem pairSieve_divisors_subsets (P : ℕ) (hP : Squarefree P) (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, f d) = ∑ a ∈ P.primeFactors.powerset, f (∏ p ∈ a, p) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hP,
    Nat.sum_divisors_filter_squarefree hP.ne_zero, Nat.factors_eq]
  simp only [List.toFinset_coe, Nat.toFinset_factors, Finset.prod_val, Function.id_def]

def pairSieveLinear (N : ℕ) (hN : 1 ≤ N) : SelbergSieve where
  support := ∅
  prodPrimes := primorial (N^2)
  prodPrimes_squarefree := squarefree_primorial _
  weights := fun _ => 0
  weights_nonneg := fun _ => le_rfl
  totalMass := 0
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := (Sieve.CompletelyMultiplicative.zeta.pdiv Sieve.CompletelyMultiplicative.id).isMultiplicative
  nu_pos_of_prime := by
    intro p hp _
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hp.ne_zero, Nat.cast_one, ArithmeticFunction.id_apply]
    exact one_div_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hp.ne_zero, Nat.cast_one, ArithmeticFunction.id_apply]
    apply (div_lt_one (by exact_mod_cast hp.pos)).mpr
    exact_mod_cast hp.one_lt
  level := (N : ℝ)^2
  one_le_level := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith

theorem pairSieveLinear_term (N : ℕ) (hN : 1 ≤ N) (d : ℕ) (hd : Squarefree d) :
    SelbergSieve.selbergTerms (pairSieveLinear N hN).toBoundingSieve d =
      pairSieveWeight pairSieveReciprocal d.primeFactors := by
  rw [SelbergSieve.selbergTerms_apply]
  have hprod : (pairSieveLinear N hN).nu d =
      ∏ p ∈ d.primeFactors, (pairSieveLinear N hN).nu p := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
    exact (pairSieveLinear N hN).nu_mult.map_prod_of_subset_primeFactors d _ subset_rfl
  rw [hprod, ← prod_mul_distrib]
  apply prod_congr rfl; intro p hp
  have hpp := (Nat.mem_primeFactors.mp hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  simp only [pairSieveLinear, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hpp.ne_zero, Nat.cast_one, ArithmeticFunction.id_apply,
    pairSieveReciprocal]
  field_simp
  <;> ring

theorem pairSieveLinear_sum (N : ℕ) (hN : 1 ≤ N) :
    (pairSieveLinear N hN).selbergBoundingSum =
      pairSieveSubsetSum (Nat.primesLE (N^2)) pairSieveReciprocal N := by
  unfold SelbergSieve.selbergBoundingSum
  change (∑ d ∈ (primorial (N^2)).divisors,
    if (d : ℝ)^2 ≤ (N : ℝ)^2 then _ else 0) = _
  rw [pairSieve_divisors_subsets _ (squarefree_primorial _), primeFactors_primorial]
  apply sum_congr rfl; intro a ha
  have hap : ∀ p ∈ a, p.Prime := fun p hp =>
    (Nat.mem_primesLE.mp ((mem_powerset.mp ha) hp)).2
  have hsq : Squarefree (∏ p ∈ a, p) := Sieve.prodDistinctPrimes_squarefree a hap
  have hle : ((∏ p ∈ a, p : ℕ) : ℝ)^2 ≤ (N : ℝ)^2 ↔ (∏ p ∈ a, p) ≤ N := by
    rw [sq_le_sq₀ (by positivity) (by positivity)]
    exact Nat.cast_le
  simp only [hle, pairSieveLinear_term N hN _ hsq, Nat.primeFactors_prod hap]

theorem pairSieveLinear_log_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log N ≤ pairSieveSubsetSum (Nat.primesLE (N^2)) pairSieveReciprocal N := by
  have he := Sieve.boundingSum_ge_log (pairSieveLinear N hN) rfl (by
    intro p hp hple
    apply (Sieve.prime_dvd_primorial_iff (N^2) p hp).mpr
    change (p : ℝ) ≤ (N : ℝ)^2 at hple
    exact_mod_cast hple)
  rw [pairSieveLinear_sum] at he
  simp only [pairSieveLinear, Real.log_pow] at he
  linarith

end
end HigherCorrelations
