import HigherCorrelations.PairSieveDenominator

/-! UNCONDITIONAL. An explicit average of the shift divisor factor. All Euler
products are finite; the constant follows from a telescoping majorant. -/
namespace HigherCorrelations
noncomputable section
open Finset

theorem pairSieveExcess_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ pairSieveExcess p := by
  unfold pairSieveExcess
  have := pairSieveReciprocal_nonneg p hp
  positivity

theorem pairSieveExcess_identity (p : ℕ) :
    1+pairSieveExcess p = (1+pairSieveReciprocal p)^2 := by
  unfold pairSieveExcess; ring

/-- Uniform convergent majorant for the divisor-factor excess. -/
theorem pairSieveExcess_majorant (p : ℕ) (hp : 2 ≤ p) :
    pairSieveExcess p / p ≤ 3 / ((p : ℝ)*((p : ℝ)-1)) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) < (p : ℝ)-1 := by linarith
  unfold pairSieveExcess pairSieveReciprocal
  have he : (2*(1/((p : ℝ)-1))+(1/((p : ℝ)-1))^2)/(p : ℝ) =
      (2*(p : ℝ)-1)/((p : ℝ)*((p : ℝ)-1)^2) := by
    field_simp
    <;> ring
  have he' : 3/((p : ℝ)*((p : ℝ)-1)) =
      (3*((p : ℝ)-1))/((p : ℝ)*((p : ℝ)-1)^2) := by
    field_simp
    <;> ring
  rw [he, he']
  apply div_le_div_of_nonneg_right _ (mul_nonneg h0.le (sq_nonneg _))
  linarith

/-- The telescoping majorant is bounded independently of the sieve cutoff. -/
theorem pairSieve_telescope (N : ℕ) :
    (∑ n ∈ Icc 2 (N+1), 1/((n : ℝ)*((n : ℝ)-1))) = 1-1/(N+1:ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [show N+1+1 = (N+1)+1 by rfl, sum_Icc_succ_top (by omega), ih]
    push_cast
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    <;> ring

theorem pairSieveExcess_sum_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, pairSieveExcess p/p) ≤ 3 := by
  have he : (∑ p ∈ Nat.primesLE N, pairSieveExcess p/p) ≤
      ∑ p ∈ Icc 2 (N+1), 3/((p : ℝ)*((p : ℝ)-1)) := by
    apply (sum_le_sum (fun p hp => pairSieveExcess_majorant p (Nat.mem_primesLE.mp hp).2.two_le)).trans
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.two_le, (Nat.mem_primesLE.mp hp).1.trans (by omega)⟩
    · intro p hp _
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
  have hid : (∑ p ∈ Icc 2 (N+1), 3/((p : ℝ)*((p : ℝ)-1))) =
      3*(1-1/(N+1:ℝ)) := by
    rw [← pairSieve_telescope N, mul_sum]
    apply sum_congr rfl; intro p hp; ring
  rw [hid] at he
  have : 0 ≤ 1/(N+1:ℝ) := by positivity
  linarith

theorem pairSieveExcess_product_le (N : ℕ) :
    (∏ p ∈ Nat.primesLE N, (1+pairSieveExcess p/p)) ≤ Real.exp 3 := by
  calc
    _ ≤ ∏ p ∈ Nat.primesLE N, Real.exp (pairSieveExcess p/p) := by
      apply prod_le_prod₀
      · intro p hp
        have := pairSieveExcess_nonneg p (Nat.mem_primesLE.mp hp).2
        positivity
      · intro p hp
        linarith [Real.add_one_le_exp (pairSieveExcess p/p)]
    _ = Real.exp (∑ p ∈ Nat.primesLE N, pairSieveExcess p/p) := by rw [Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (pairSieveExcess_sum_le N)

/-- Exact count of positive multiples in a closed integer interval. -/
theorem pairSieve_multiples_card (N d : ℕ) (hd : 0 < d) :
    ((Icc 1 N).filter (fun n => d ∣ n)).card = N/d := by
  have he : (Icc 1 N).filter (fun n => d ∣ n) = (Icc 1 (N/d)).image (fun k => d*k) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hdn⟩
      refine ⟨n/d, ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd, Nat.div_le_div_right hnN⟩, ?_⟩
      exact Nat.mul_div_cancel' hdn
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      exact ⟨⟨Nat.mul_pos hd hk1, (Nat.mul_le_mul_left d hkN).trans (Nat.mul_div_le N d)⟩,
        dvd_mul_right d k⟩
  rw [he, card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hd hab)]
  simp

/-- Finite squarefree expansion of the divisor factor, on a common prime set. -/
theorem pairSieveBadFactor_expansion (N h : ℕ) (hh : h ∈ Icc 1 N) :
    pairSieveBadFactor h = ∑ a ∈ (Nat.primesLE N).powerset,
      if (∏ p ∈ a, p) ∣ h then pairSieveWeight pairSieveExcess a else 0 := by
  have hh0 : h ≠ 0 := by have := (mem_Icc.mp hh).1; omega
  let s := Nat.primesLE N
  have hsub : h.primeFactors ⊆ s := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans (mem_Icc.mp hh).2,
      (Nat.mem_primeFactors.mp hp).1⟩
  have he : pairSieveBadFactor h = ∏ p ∈ s,
      (1 + if p ∣ h then pairSieveExcess p else 0) := by
    unfold pairSieveBadFactor
    rw [← prod_subset hsub]
    · apply prod_congr rfl; intro p hp
      rw [ite_eq_left (Nat.mem_primeFactors.mp hp).2.1, pairSieveExcess_identity]
    · intro p hp hph
      have hpnd : ¬p ∣ h := fun hd => hph (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primesLE.mp hp).2, hd, hh0⟩)
      simp [hpnd]
  rw [he, prod_one_add]
  apply sum_congr rfl; intro a ha
  by_cases hd : (∏ p ∈ a, p) ∣ h
  · rw [ite_eq_left hd]
    apply prod_congr rfl; intro p hp
    exact ite_eq_left ((dvd_prod_of_mem (fun p : ℕ => p) hp).trans hd)
  · rw [ite_eq_right hd]
    have hex : ∃ p ∈ a, ¬p ∣ h := by
      by_contra hn
      push Not at hn
      apply hd
      exact Sieve.prod_primes_dvd_of_dvd h hn
        (fun p hp => (Nat.mem_primesLE.mp ((mem_powerset.mp ha) hp)).2)
    obtain ⟨p, hp, hph⟩ := hex
    apply prod_eq_zero hp
    exact ite_eq_right hph

/-- Absolute effective average, including h=1 and an empty shift range. -/
theorem pairSieveBadFactor_sum_le (N : ℕ) :
    (∑ h ∈ Icc 1 N, pairSieveBadFactor h) ≤ Real.exp 3 * N := by
  have he : (∑ h ∈ Icc 1 N, pairSieveBadFactor h) =
      ∑ a ∈ (Nat.primesLE N).powerset,
        pairSieveWeight pairSieveExcess a * ((N/(∏ p ∈ a, p) : ℕ) : ℝ) := by
    simp_rw [sum_congr rfl (fun h hh => pairSieveBadFactor_expansion N h hh)]
    rw [sum_comm]
    apply sum_congr rfl; intro a ha
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hd : 0 < ∏ p ∈ a, p := prod_pos
      (fun p hp => (Nat.mem_primesLE.mp ((mem_powerset.mp ha) hp)).2.pos)
    rw [pairSieve_multiples_card N _ hd, mul_comm]
  rw [he]
  calc
    _ ≤ ∑ a ∈ (Nat.primesLE N).powerset,
        pairSieveWeight pairSieveExcess a * ((N : ℝ)/(∏ p ∈ a, p : ℕ)) := by
      apply sum_le_sum; intro a ha
      apply mul_le_mul_of_nonneg_left Nat.cast_div_le
      exact prod_nonneg (fun p hp => pairSieveExcess_nonneg p
        (Nat.mem_primesLE.mp ((mem_powerset.mp ha) hp)).2)
    _ = (N : ℝ) * ∏ p ∈ Nat.primesLE N, (1+pairSieveExcess p/p) := by
      rw [prod_one_add, mul_sum]
      apply sum_congr rfl; intro a ha
      simp only [pairSieveWeight, prod_div_distrib, Nat.cast_prod]
      ring
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (pairSieveExcess_product_le N) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      simpa [mul_comm] using this
end
end HigherCorrelations
