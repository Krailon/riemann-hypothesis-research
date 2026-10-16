import HigherCorrelations.PairSieveDefinitions
import OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound

/-! UNCONDITIONAL. Local arithmetic for the shifted polynomial n(n+h).
Residue negation identifies its roots with the already checked Goldbach local
model; the integer interval and prime-pair set are different and are rebuilt. -/
namespace HigherCorrelations
noncomputable section
open Finset OAI.Problem337

/-- Negating the residue preserves the local root cardinality. -/
theorem pairSieve_root_card (h d : ℕ) [NeZero d] :
    (univ.filter (fun x : ZMod d => x * (x + h) = 0)).card =
      goldbachSieveRootCount h d := by
  classical
  rw [goldbachSieveRootCount_eq_filter_card]
  apply card_equiv (Equiv.neg (ZMod d))
  intro x
  simp only [mem_filter, mem_univ, true_and, Equiv.neg_apply]
  have he : -x * ((h : ZMod d) - -x) = -(x * (x+h)) := by ring
  rw [he, neg_eq_zero]

theorem pairSieve_polynomial_discrepancy (U h d : ℕ) [NeZero d] :
    |(((Icc 1 U).filter (fun n => d ∣ n*(n+h))).card : ℝ) -
      goldbachSieveDensity h d * U| ≤ goldbachSieveRootCount h d := by
  classical
  have hf : (Icc 1 U).filter (fun n => d ∣ n*(n+h)) =
      (Ico 1 (1+U)).filter (fun n : ℕ => (n : ZMod d)*((n : ZMod d)+h)=0) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_Ico]
    rw [← Nat.cast_add, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    omega
  have he := zmod_predicate_Ico_discrepancy d
    (fun x : ZMod d => x*(x+h)=0) 1 U
  rw [hf, ← pairSieve_root_card h d]
  simpa only [goldbachSieveDensity_apply, pairSieve_root_card,
    div_mul_eq_mul_div, mul_comm, mul_div_assoc] using he

/-- Multiplicities of polynomial values are retained by the image sieve. -/
def pairSieve (U h P : ℕ) (hh : 2 ∣ h) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 U) (fun n => n*(n+h)) P hP
    (goldbachSieveDensity h) (goldbachSieveDensity_isMultiplicative h)
    (fun p hp _ => goldbachSieveDensity_prime_pos h p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one h p hp (fun _ => hh))

theorem pairSieve_normalizer (U h P z : ℕ) (hh : 2 ∣ h) (hP : Squarefree P) :
    SelbergOptimal.normalizer (pairSieve U h P hh hP) z =
      GoldbachSelberg.denominator h P z := by
  unfold SelbergOptimal.normalizer GoldbachSelberg.denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem pairSieve_rem (U h P d : ℕ) (hh : 2 ∣ h) (hP : Squarefree P) [NeZero d] :
    |(pairSieve U h P hh hP).rem d| ≤ goldbachSieveRootCount h d := by
  unfold pairSieve
  rw [PrimePairSieve.imageSieve_rem]
  simpa using pairSieve_polynomial_discrepancy U h d

theorem pairSieve_rem_lcm (U h P : ℕ) (hh : 2 ∣ h) (hP : Squarefree P)
    (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(pairSieve U h P hh hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ)^a.primeFactors.card * (2 : ℝ)^b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := goldbachSieveRootCount_le_two_pow h a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow h b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount h (Nat.lcm a b) : ℝ) := pairSieve_rem U h P _ hh hP
    _ ≤ (goldbachSieveRootCount h a : ℝ)*goldbachSieveRootCount h b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le h a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

/-- Exact small-prime exceptions, also valid at h=0 and empty intervals. -/
theorem pairSieve_primes_subset (U h P : ℕ) (hP : P ≠ 0) :
    pairSievePrimes U h ⊆ pairSieveSifted U h P ∪
      (P.primeFactors ∪ P.primeFactors.image (fun p => p-h)) := by
  classical
  intro n hn
  obtain ⟨hnI, hnp, hnhp⟩ := mem_filter.mp hn
  by_cases hd : n ∣ P
  · exact mem_union_right _ (mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hnp, hd, hP⟩))
  by_cases hd' : n+h ∣ P
  · exact mem_union_right _ (mem_union_right _ (mem_image.mpr
      ⟨n+h, Nat.mem_primeFactors.mpr ⟨hnhp, hd', hP⟩, Nat.add_sub_cancel n h⟩))
  exact mem_union_left _ (mem_filter.mpr ⟨hnI,
    (hnp.coprime_iff_not_dvd.mpr hd).symm.mul_right
      (hnhp.coprime_iff_not_dvd.mpr hd').symm⟩)

theorem pairSieve_primes_le_sifted (U h P : ℕ) (hP : P ≠ 0) :
    (pairSievePrimes U h).card ≤ (pairSieveSifted U h P).card + 2*P.primeFactors.card := by
  classical
  have ha := card_le_card (pairSieve_primes_subset U h P hP)
  have hb := card_union_le (pairSieveSifted U h P)
    (P.primeFactors ∪ P.primeFactors.image (fun p => p-h))
  have hc := card_union_le P.primeFactors (P.primeFactors.image (fun p => p-h))
  have hd := card_image_le (s := P.primeFactors) (f := fun p => p-h)
  omega

/-- Finite unconditional shifted-prime upper sieve with an actual denominator. -/
theorem pairSieve_primes_le (U h P : ℕ) (hh : 2 ∣ h) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) :
    ((pairSievePrimes U h).card : ℝ) ≤
      U / GoldbachSelberg.denominator h P z +
      (z : ℝ)^2*(1+Real.log z)^4 + 2*P.primeFactors.card := by
  have he := SelbergOptimal.siftedSum_le_log_error (pairSieve U h P hh hP) hz
    (fun a ha b hb => pairSieve_rem_lcm U h P hh hP a ha b hb)
  have hs : (pairSieve U h P hh hP).siftedSum = ((pairSieveSifted U h P).card : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hm : (pairSieve U h P hh hP).totalMass = (U : ℝ) := by
    simp [pairSieve, PrimePairSieve.imageSieve]
  rw [hs, hm, pairSieve_normalizer] at he
  have hp : ((pairSievePrimes U h).card : ℝ) ≤
      (pairSieveSifted U h P).card + 2*P.primeFactors.card := by
    exact_mod_cast pairSieve_primes_le_sifted U h P hP.ne_zero
  linarith

theorem pairSieve_primes_le_primorial (U h : ℕ) (hh : 2 ∣ h)
    {z : ℕ} (hz : 1 ≤ z) :
    ((pairSievePrimes U h).card : ℝ) ≤
      U / GoldbachSelberg.denominator h (primorial z) z +
      (z : ℝ)^2*(1+Real.log z)^4 + 2*(Nat.primesLE z).card := by
  simpa only [primeFactors_primorial] using
    pairSieve_primes_le U h (primorial z) hh (squarefree_primorial z) hz
end
end HigherCorrelations
