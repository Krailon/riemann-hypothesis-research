import HigherCorrelations.PairSieveLinear
import HigherCorrelations.PairSieveLocal

/-! UNCONDITIONAL. An explicit dimension-two denominator lower bound.
The shift factor includes p=2; for even h it is four times the odd-prime factor.
No estimate on the distribution of primes is assumed. -/
namespace HigherCorrelations
noncomputable section
open Finset OAI.Problem337

theorem pairSieveLocalWeight_pos (h p : ℕ) (hh : 2 ∣ h) (hp : p.Prime) :
    0 < pairSieveLocalWeight h p := by
  unfold pairSieveLocalWeight
  exact mul_pos (goldbachSieveDensity_prime_pos h p hp)
    (inv_pos.mpr (sub_pos.mpr (goldbachSieveDensity_prime_lt_one h p hp (fun _ => hh))))

theorem pairSieve_denominator_subsets (h P z : ℕ) (hP : Squarefree P) :
    GoldbachSelberg.denominator h P z =
      pairSieveSubsetSum P.primeFactors (pairSieveLocalWeight h) z := by
  unfold GoldbachSelberg.denominator
  rw [pairSieve_divisors_subsets _ hP]
  apply sum_congr rfl; intro a ha
  have hap : ∀ p ∈ a, p.Prime := fun p hp =>
    (Nat.mem_primeFactors.mp ((mem_powerset.mp ha) hp)).1
  rw [Nat.primeFactors_prod hap]
  have he : goldbachSieveDensity h (∏ p ∈ a, p) = ∏ p ∈ a, goldbachSieveDensity h p :=
    (goldbachSieveDensity_isMultiplicative h).map_prod_of_subset_primeFactors P a (mem_powerset.mp ha)
  rw [he, ← prod_mul_distrib]
  rfl

theorem pairSieveReciprocal_nonneg (p : ℕ) (hp : p.Prime) :
    0 ≤ pairSieveReciprocal p := by
  unfold pairSieveReciprocal
  have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  positivity

theorem pairSieveBadFactor_one_le (h : ℕ) : 1 ≤ pairSieveBadFactor h := by
  apply one_le_prod₀
  intro p hp
  have := pairSieveReciprocal_nonneg p (Nat.mem_primeFactors.mp hp).1
  nlinarith

/-- At a prime not dividing the shift, the union-convolution weight is smaller
than the actual two-root sieve weight. -/
theorem pairSieve_good_weight (h p : ℕ) (hh : 2 ∣ h) (hp : p.Prime) (hph : ¬p ∣ h) :
    2*pairSieveReciprocal p + pairSieveReciprocal p^2 ≤ pairSieveLocalWeight h p := by
  have hp2 : 2 < p := by
    have := hp.two_le
    by_contra hn
    have : p = 2 := by omega
    exact hph (this ▸ hh)
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
  unfold pairSieveReciprocal pairSieveLocalWeight
  rw [goldbachSieveDensity_prime h p hp, ite_eq_right hph]
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ)-1 > 0 := by linarith
  have h2 : (p : ℝ)-2 > 0 := by linarith
  have he : (2/(p : ℝ))*(1-2/(p : ℝ))⁻¹ = 2/((p : ℝ)-2) := by
    field_simp <;> ring
  rw [he]
  apply (le_div_iff₀ h2).mpr
  have he' : (2*(1/((p : ℝ)-1))+(1/((p : ℝ)-1))^2)*((p : ℝ)-2) =
      (((2*(p : ℝ)-1)*((p : ℝ)-2))/((p : ℝ)-1)^2) := by
    field_simp <;> ring
  rw [he']
  apply (div_le_iff₀ (sq_pos_of_pos h1)).mpr
  nlinarith

/-- A uniform logarithmic-square lower bound at a squared integer cutoff. -/
theorem pairSieve_denominator_lower (h N : ℕ) (hh : 2 ∣ h) (hh0 : h ≠ 0) (hN : 1 ≤ N) :
    Real.log N ^ 2 ≤ pairSieveBadFactor h *
      GoldbachSelberg.denominator h (primorial (N^2)) (N^2) := by
  let s := Nat.primesLE (N^2)
  let q := fun p : ℕ => ¬p ∣ h
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hsq := pairSieveSubsetSum_sq_le s pairSieveReciprocal N
    (fun p hp => (hs p hp).one_lt.le)
    (fun p hp => pairSieveReciprocal_nonneg p (hs p hp)) q
  have hbad : (∏ p ∈ s.filter (fun p => ¬q p), (1+pairSieveReciprocal p)^2) ≤
      pairSieveBadFactor h := by
    apply prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      obtain ⟨hp, hph⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hs p hp, Classical.not_not.mp hph, hh0⟩
    · intro p hp; positivity
    · intro p hp _
      have := pairSieveReciprocal_nonneg p (Nat.mem_primeFactors.mp hp).1
      nlinarith
  have hgood : pairSieveSubsetSum (s.filter q)
      (fun p => 2*pairSieveReciprocal p+pairSieveReciprocal p^2) (N^2) ≤
      GoldbachSelberg.denominator h (primorial (N^2)) (N^2) := by
    rw [pairSieve_denominator_subsets _ _ _ (squarefree_primorial _), primeFactors_primorial]
    unfold pairSieveSubsetSum
    calc
      _ ≤ ∑ a ∈ (s.filter q).powerset,
          if (∏ p ∈ a, p) ≤ N^2 then pairSieveWeight (pairSieveLocalWeight h) a else 0 := by
        apply sum_le_sum; intro a ha
        split_ifs
        · apply prod_le_prod₀
          · intro p hp
            have := pairSieveReciprocal_nonneg p (hs p (mem_filter.mp ((mem_powerset.mp ha) hp)).1)
            positivity
          · intro p hp
            obtain ⟨hps, hph⟩ := mem_filter.mp ((mem_powerset.mp ha) hp)
            exact pairSieve_good_weight h p hh (hs p hps) hph
        · rfl
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (powerset_mono.mpr (filter_subset _ _))
        intro a ha _
        split_ifs
        · exact prod_nonneg (fun p hp => (pairSieveLocalWeight_pos h p hh
            (hs p ((mem_powerset.mp ha) hp))).le)
        · rfl
  calc
    Real.log N^2 ≤ pairSieveSubsetSum s pairSieveReciprocal N ^ 2 := by
      apply pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hN))
      exact pairSieveLinear_log_le N hN
    _ ≤ _ := hsq.trans (mul_le_mul hbad hgood
      (pairSieveSubsetSum_nonneg _ _ _ (by
        intro p hp
        have := pairSieveReciprocal_nonneg p (hs p (mem_filter.mp hp).1)
        positivity)) (pairSieveBadFactor_one_le h |>.trans' (by norm_num)))
end
end HigherCorrelations
